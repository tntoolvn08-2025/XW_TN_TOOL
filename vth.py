from __future__ import annotations
import json
import sys
import time
import threading
import random
import logging
import math
import re
from collections import defaultdict, deque
from datetime import datetime
from pathlib import Path
from urllib.parse import urlparse, parse_qs
from typing import Any, Dict, Tuple, Optional

import pytz
import requests
import websocket
from rich.console import Console, Group
from rich.table import Table
from rich.panel import Panel
from rich.live import Live
from rich.align import Align
from rich.prompt import Prompt, IntPrompt, FloatPrompt
from rich.rule import Rule
from rich.text import Text
from rich import box
from rich.columns import Columns

console = Console()
tz = pytz.timezone("Asia/Ho_Chi_Minh")

logger = logging.getLogger("escape_vip_ai_rebuild")
logger.setLevel(logging.INFO)
logger.addHandler(logging.FileHandler("escape_vip_ai_rebuild.log", encoding="utf-8"))

BET_API_URL = "https://api.escapemaster.net/escape_game/bet"
WS_URL = "wss://api.escapemaster.net/escape_master/ws"
WALLET_API_URL = "https://wallet.3games.io/api/wallet/user_asset"

HTTP = requests.Session()
try:
    from requests.adapters import HTTPAdapter
    from urllib3.util.retry import Retry
    adapter = HTTPAdapter(
        pool_connections=20, pool_maxsize=50,
        max_retries=Retry(total=3, backoff_factor=0.2,
                          status_forcelist=(500, 502, 503, 504))
    )
    HTTP.mount("https://", adapter)
    HTTP.mount("http://", adapter)
except Exception:
    pass

ROOM_NAMES = {
    1: "📦 Nhà kho", 2: "🪑 Phòng họp", 3: "👔 Phòng giám đốc", 4: "💬 Phòng trò chuyện",
    5: "🎥 Phòng giám sát", 6: "🏢 Văn phòng", 7: "💰 Phòng tài vụ", 8: "👥 Phòng nhân sự"
}
ROOM_ORDER = [1, 2, 3, 4, 5, 6, 7, 8]

USER_ID: Optional[int] = None
SECRET_KEY: Optional[str] = None
issue_id: Optional[int] = None
issue_start_ts: Optional[float] = None
issue_end_ts: Optional[float] = None
count_down: Optional[int] = None
killed_room: Optional[int] = None
round_index: int = 0

room_state: Dict[int, Dict[str, Any]] = {r: {"players": 0, "bet": 0} for r in ROOM_ORDER}
room_stats: Dict[int, Dict[str, Any]] = {r: {"kills": 0, "survives": 0, "last_kill_round": None, "last_players": 0, "last_bet": 0} for r in ROOM_ORDER}

predicted_room: Optional[int] = None
last_killed_room: Optional[int] = None
prediction_locked: bool = False

current_build: Optional[float] = None
current_usdt: Optional[float] = None
current_world: Optional[float] = None
last_balance_ts: Optional[float] = None
last_balance_val: Optional[float] = None
starting_balance: Optional[float] = None
cumulative_profit: Optional[float] = None

win_streak: int = 0
lose_streak: int = 0
max_win_streak: int = 0
max_lose_streak: int = 0

base_bet: float = 1.0
multiplier: float = 2.0
current_bet: Optional[float] = None
run_mode: str = "AUTO"
bet_rounds_before_skip: int = 0
_rounds_placed_since_skip: int = 0
skip_next_round_flag: bool = False

bet_history: deque = deque(maxlen=200)
bet_sent_for_issue: set = set()

pause_after_losses: int = 0
_skip_rounds_remaining: int = 0
profit_target: Optional[float] = None
stop_when_profit_reached: bool = False
stop_loss_target: Optional[float] = None
stop_when_loss_reached: bool = False
stop_flag: bool = False

ui_state: str = "IDLE"
analysis_duration: float = 45.0
analysis_start_ts: Optional[float] = None

last_msg_ts: float = time.time()
last_balance_fetch_ts: float = 0.0
BALANCE_POLL_INTERVAL: float = 4.0
_ws: Dict[str, Any] = {"ws": None}

_sequential_bet_index = 0
killer_history = deque(maxlen=20)
game_kill_log = deque(maxlen=10)

SELECTION_CONFIG = {
    "max_bet_allowed": float("inf"),
    "max_players_allowed": 9999,
    "avoid_last_kill": True,
}

SELECTION_MODES = {
    "RANDOM": "1. PHẬT ĐỘ (Ngẫu nhiên)",
    "MIN_PLAYER_BET": "2. AN TOÀN TRÊN HẾT (ÍT BUILD & NGƯỜI)",
    "PROBABILITY": "3. Xác suất (Né phòng hay bị giết)",
    "FOLLOW_KILLER": "4. Theo phòng sát thủ vừa vào",
    "SEQUENTIAL": "5. Theo thứ tự từ 1 đến 8",
    "KILLER_PERSONALITY": "6. Học hỏi tính cách sát thủ (AI)",
    "SMART_SAFE": "7. Tính toán an toàn thông minh (AI)",
    "VIP_10": "8. VIP 10 công thức né sát thủ (AI)",
    "HIDE_SEEK_MASTER": "9. Thánh trốn tìm (AI)",
}

settings = {"algo": "RANDOM"}

STRATEGY_CONFIG_FILE = "strategy_vth.json"

_spinner = ["📦", "🪑", "👔", "💬", "🎥", "🏢", "💰", "👥"]

_num_re = re.compile(r"-?\d+[\d,]*\.?\d*")

VIP_COLORS = ["#FF00FF", "#D700FF", "#AF00FF", "#8700FF", "#5F00FF", "#0000FF", "#005FFF", "#0087FF", "#00AFFF", "#00D7FF", "#00FFFF"]

ENABLE_ENHANCEMENTS = False

def slow_print(text: str, delay: float = 0.01, style: Optional[str] = None):
    for char in text:
        console.print(Text(char, style=style or "default"), end="")
        time.sleep(delay)
    console.print()

def log_debug(msg: str):
    try:
        logger.debug(msg)
    except Exception:
        pass

def _parse_number(x: Any) -> Optional[float]:
    if x is None:
        return None
    if isinstance(x, (int, float)):
        return float(x)
    s = str(x)
    m = _num_re.search(s)
    if not m:
        return None
    token = m.group(0).replace(",", "")
    try:
        return float(token)
    except Exception:
        return None

def human_ts() -> str:
    return datetime.now(tz).strftime("%Y-%m-%d %H:%M:%S")

def safe_input(prompt: str, default=None, cast=None):
    try:
        s = input(prompt).strip()
    except EOFError:
        return default
    if s == "":
        return default
    if cast:
        try:
            return cast(s)
        except Exception:
            return default
    return s

def _parse_balance_from_json(j: Dict[str, Any]) -> Tuple[Optional[float], Optional[float], Optional[float]]:
    if not isinstance(j, dict):
        return None, None, None
    build = None
    world = None
    usdt = None

    data = j.get("data") if isinstance(j.get("data"), dict) else j
    if isinstance(data, dict):
        cwallet = data.get("cwallet") if isinstance(data.get("cwallet"), dict) else None
        if cwallet:
            for key in ("ctoken_contribute", "ctoken", "build", "balance", "amount"):
                if key in cwallet and build is None:
                    build = _parse_number(cwallet.get(key))
        for k in ("build", "ctoken", "ctoken_contribute"):
            if build is None and k in data:
                build = _parse_number(data.get(k))
        for k in ("usdt", "kusdt", "usdt_balance"):
            if usdt is None and k in data:
                usdt = _parse_number(data.get(k))
        for k in ("world", "xworld"):
            if world is None and k in data:
                world = _parse_number(data.get(k))

    found = []

    def walk(o: Any, path=""):
        if isinstance(o, dict):
            for kk, vv in o.items():
                nk = (path + "." + str(kk)).strip(".")
                if isinstance(vv, (dict, list)):
                    walk(vv, nk)
                else:
                    n = _parse_number(vv)
                    if n is not None:
                        found.append((nk.lower(), n))
        elif isinstance(o, list):
            for idx, it in enumerate(o):
                walk(it, f"{path}[{idx}]")

    walk(j)

    for k, n in found:
        if build is None and any(x in k for x in ("ctoken", "build", "contribute", "balance")):
            build = n
        if usdt is None and "usdt" in k:
            usdt = n
        if world is None and any(x in k for x in ("world", "xworld")):
            world = n

    return build, world, usdt

def balance_headers_for(uid: Optional[int] = None, secret: Optional[str] = None) -> Dict[str, str]:
    h = {
        "accept": "*/*",
        "accept-language": "vi,en;q=0.9",
        "cache-control": "no-cache",
        "country-code": "vn",
        "origin": "https://xworld.info",
        "pragma": "no-cache",
        "referer": "https://xworld.info/",
        "user-agent": "Mozilla/5.0 (Linux; Android 6.0; Nexus 5) AppleWebKit/537.36 "
                      "(KHTML, like Gecko) Chrome/137.0.0.0 Mobile Safari/537.36",
        "user-login": "login_v2",
        "xb-language": "vi-VN",
    }
    if uid is not None:
        h["user-id"] = str(uid)
    if secret:
        h["user-secret-key"] = str(secret)
    return h

def fetch_balances_3games(retries=3, timeout=8, params=None, uid=None, secret=None):
    global current_build, current_usdt, current_world, last_balance_ts
    global starting_balance, last_balance_val, cumulative_profit

    uid = uid or USER_ID
    secret = secret or SECRET_KEY
    payload = {"user_id": int(uid) if uid is not None else None, "source": "home"}

    attempt = 0
    while attempt <= retries:
        attempt += 1
        try:
            r = HTTP.post(
                WALLET_API_URL,
                json=payload,
                headers=balance_headers_for(uid, secret),
                timeout=timeout,
            )
            r.raise_for_status()
            j = r.json()

            data = j.get("data", {}) if isinstance(j, dict) else {}
            ua = data.get("user_asset", {}) if isinstance(data, dict) else {}

            build = _parse_number(ua.get("BUILD"))
            world = _parse_number(ua.get("WORLD"))
            usdt  = _parse_number(ua.get("USDT"))

            if build is not None:
                if last_balance_val is None:
                    starting_balance = build
                    last_balance_val = build
                else:
                    last_balance_val = build
                current_build = build
                if starting_balance is not None:
                    cumulative_profit = current_build - starting_balance

            if usdt is not None:
                current_usdt = usdt
            if world is not None:
                current_world = world

            last_balance_ts = time.time()
            return current_build, current_world, current_usdt

        except Exception as e:
            log_debug(f"wallet fetch attempt {attempt} error: {e}")
            time.sleep(min(1.5 * attempt, 4))

    return current_build, current_world, current_usdt

def choose_random() -> int:
    """Chọn một phòng ngẫu nhiên."""
    return random.choice(ROOM_ORDER)

def choose_min_player_bet() -> int:
    """Chọn phòng có ít người chơi và ít tiền cược nhất."""
    if not any(rs.get('players', 0) > 0 or rs.get('bet', 0) > 0 for rs in room_state.values()):
        return choose_random()
    
    player_ranks = sorted(ROOM_ORDER, key=lambda r: room_state[r]['players'])
    bet_ranks = sorted(ROOM_ORDER, key=lambda r: room_state[r]['bet'])

    scores = defaultdict(int)
    for i, r in enumerate(player_ranks):
        scores[r] += i
    for i, r in enumerate(bet_ranks):
        scores[r] += i
    
    if last_killed_room in scores:
        scores[last_killed_room] += 0.5

    return min(scores, key=scores.get)

def choose_probability() -> int:
    """Chọn phòng có tỷ lệ sống sót cao nhất trong lịch sử."""
    scores = {}
    for r in ROOM_ORDER:
        kills = room_stats[r].get('kills', 0)
        survives = room_stats[r].get('survives', 0)
        survival_rate = (survives + 1) / (kills + survives + 2)
        scores[r] = survival_rate

    return max(scores, key=scores.get)

def choose_follow_killer() -> int:
    """Cược vào phòng vừa bị sát thủ giết."""
    if last_killed_room is not None and last_killed_room in ROOM_ORDER:
        return last_killed_room
    return random.choice(ROOM_ORDER)

def choose_sequential() -> int:
    """Cược lần lượt từ phòng 1 đến 8."""
    global _sequential_bet_index
    room_to_bet = ROOM_ORDER[_sequential_bet_index]
    _sequential_bet_index = (_sequential_bet_index + 1) % len(ROOM_ORDER)
    return room_to_bet

def choose_killer_personality() -> int:
    """Học hỏi thói quen của sát thủ và né."""
    if not killer_history:
        return choose_random()

    avg_players = sum(h['players'] for h in killer_history) / len(killer_history)
    avg_bet = sum(h['bet'] for h in killer_history) / len(killer_history)

    avoidance_scores = {}
    for r in ROOM_ORDER:
        if r == last_killed_room:
            avoidance_scores[r] = -999999
            continue
        
        current_players = room_state[r]['players']
        current_bet = room_state[r]['bet']
        
        player_dist = abs(current_players - avg_players) / (avg_players + 1)
        bet_dist = abs(current_bet - avg_bet) / (avg_bet + 1)
        
        avoidance_scores[r] = player_dist + bet_dist

    return max(avoidance_scores, key=avoidance_scores.get)

def choose_smart_safe() -> int:
    """Tính toán an toàn dựa trên người, tiền, và lịch sử."""
    scores = {}
    
    max_players = max(rs['players'] for rs in room_state.values()) or 1
    max_bet = max(rs['bet'] for rs in room_state.values()) or 1

    for r in ROOM_ORDER:
        kills = room_stats[r].get('kills', 0)
        survives = room_stats[r].get('survives', 0)
        survival_rate = (survives + 1) / (kills + survives + 2)

        player_score = 1 - (room_state[r]['players'] / max_players)
        bet_score = 1 - (room_state[r]['bet'] / max_bet)
        last_kill_penalty = 0.5 if r == last_killed_room else 0

        final_score = (0.4 * survival_rate) + (0.3 * player_score) + (0.3 * bet_score) - last_kill_penalty
        scores[r] = final_score

    return max(scores, key=scores.get)

def choose_vip_10() -> int:
    """Áp dụng 10 công thức né sát thủ bằng cách lọc các ứng viên."""
    candidates = set(ROOM_ORDER)
    
    # Rule 1: Né phòng vừa bị giết
    if last_killed_room in candidates: candidates.remove(last_killed_room)

    # Rule 2: Né phòng có nhiều người chơi nhất (mục tiêu đám đông)
    if len(candidates) > 1:
        try:
            most_players_room = max(candidates, key=lambda r: room_state.get(r, {}).get('players', 0))
            candidates.remove(most_players_room)
        except (ValueError, KeyError): pass

    # Rule 3: Né phòng có nhiều tiền cược nhất (mục tiêu tiền lớn)
    if len(candidates) > 1:
        try:
            most_bet_room = max(candidates, key=lambda r: room_state.get(r, {}).get('bet', 0))
            candidates.remove(most_bet_room)
        except (ValueError, KeyError): pass

    # Rule 4: Né phòng có tỷ lệ bị giết trong lịch sử cao nhất
    if len(candidates) > 1:
        try:
            kill_rates = {r: (room_stats.get(r, {}).get('kills', 0) + 1) / (room_stats.get(r, {}).get('kills', 0) + room_stats.get(r, {}).get('survives', 0) + 2) for r in candidates}
            if kill_rates: candidates.remove(max(kill_rates, key=kill_rates.get))
        except (ValueError, KeyError): pass

    # Rule 5: Né phòng có BPP (cược/người) cao nhất (bẫy cá voi)
    if len(candidates) > 1:
        try:
            bpp = {r: (room_state.get(r, {}).get('bet', 0) / room_state.get(r, {}).get('players', 1)) if room_state.get(r, {}).get('players', 0) > 0 else 0 for r in candidates}
            if bpp: candidates.remove(max(bpp, key=bpp.get))
        except (ValueError, KeyError): pass
    
    # Rule 6: Né phòng có ít người chơi nhất (bẫy phòng vắng)
    if len(candidates) > 1:
        try:
            least_players_room = min(candidates, key=lambda r: room_state.get(r, {}).get('players', 0))
            candidates.remove(least_players_room)
        except (ValueError, KeyError): pass
            
    # Rule 7: Né phòng có lượng người chơi tăng đột biến (bẫy lùa gà)
    if len(candidates) > 1:
        try:
            deltas = {r: room_state.get(r, {}).get('players', 0) - room_stats.get(r, {}).get('last_players', 0) for r in candidates}
            if any(d > 5 for d in deltas.values()): candidates.remove(max(deltas, key=deltas.get))
        except (ValueError, KeyError): pass

    # Rule 8: Né phòng đã bị giết 2 ván trước (tránh lặp mẫu)
    if len(game_kill_log) >= 2 and game_kill_log[-2] in candidates: candidates.remove(game_kill_log[-2])

    # Fallback: nếu lọc hết, chọn ngẫu nhiên trong số các phòng ban đầu trừ phòng vừa bị giết
    if not candidates:
        fallback_candidates = set(ROOM_ORDER)
        if last_killed_room in fallback_candidates: fallback_candidates.remove(last_killed_room)
        if fallback_candidates: return random.choice(list(fallback_candidates))
        return choose_random() # Fallback cuối cùng
    
    return random.choice(list(candidates))

def choose_hide_seek_master() -> int:
    """Logic 'Thánh trốn tìm' - kết hợp nhiều yếu tố để tìm nơi an toàn nhất."""
    danger_scores = {}

    max_players = max(rs['players'] for rs in room_state.values()) or 1
    max_bet = max(rs['bet'] for rs in room_state.values()) or 1
    
    avg_players_killed = 0
    avg_bet_killed = 0
    if killer_history:
        avg_players_killed = sum(h['players'] for h in killer_history) / len(killer_history)
        avg_bet_killed = sum(h['bet'] for h in killer_history) / len(killer_history)

    for r in ROOM_ORDER:
        kills = room_stats[r].get('kills', 0)
        survives = room_stats[r].get('survives', 0)
        hist_danger = (kills + 1) / (kills + survives + 2)

        crowd_danger = room_state[r]['players'] / max_players
        money_danger = room_state[r]['bet'] / max_bet

        personality_danger = 0
        if killer_history:
            player_sim = 1 - (abs(room_state[r]['players'] - avg_players_killed) / (avg_players_killed + max_players + 1))
            bet_sim = 1 - (abs(room_state[r]['bet'] - avg_bet_killed) / (avg_bet_killed + max_bet + 1))
            personality_danger = (player_sim + bet_sim) / 2

        recency_penalty = 1.0 if r == last_killed_room else 0.0
        
        total_danger = (0.3 * hist_danger) + (0.2 * crowd_danger) + (0.2 * money_danger) + (0.3 * personality_danger) + recency_penalty
        danger_scores[r] = total_danger

    return min(danger_scores, key=danger_scores.get)

def choose_room_tn(mode: str) -> Tuple[int, str]:
    """Hàm điều phối chính cho các logic cược mới."""
    mode = mode.upper()
    
    logic_map = {
        "RANDOM": choose_random,
        "MIN_PLAYER_BET": choose_min_player_bet,
        "PROBABILITY": choose_probability,
        "FOLLOW_KILLER": choose_follow_killer,
        "SEQUENTIAL": choose_sequential,
        "KILLER_PERSONALITY": choose_killer_personality,
        "SMART_SAFE": choose_smart_safe,
        "VIP_10": choose_vip_10,
        "HIDE_SEEK_MASTER": choose_hide_seek_master,
    }

    func = logic_map.get(mode, choose_random)
    chosen_room = func()
    
    return chosen_room, mode

def api_headers() -> Dict[str, str]:
    return {
        "content-type": "application/json",
        "user-agent": "Mozilla/5.0",
        "user-id": str(USER_ID) if USER_ID else "",
        "user-secret-key": SECRET_KEY if SECRET_KEY else ""
    }

def place_bet_http(issue: int, room_id: int, amount: float) -> dict:
    payload = {"asset_type": "BUILD", "user_id": USER_ID, "room_id": int(room_id), "bet_amount": float(amount)}
    try:
        r = requests.post(BET_API_URL, headers=api_headers(), json=payload, timeout=8)
        try:
            return r.json()
        except Exception:
            return {"raw": r.text, "http_status": r.status_code}
    except Exception as e:
        return {"error": str(e)}

def record_bet(issue: int, room_id: int, amount: float, resp: dict, algo_used: Optional[str] = None) -> dict:
    now = datetime.now(tz).strftime("%H:%M:%S")
    rec = {"issue": issue, "room": room_id, "amount": float(amount), "time": now, "resp": resp, "result": "Đang", "algo": algo_used, "delta": 0.0, "win_streak": win_streak, "lose_streak": lose_streak}
    bet_history.append(rec)
    return rec

def place_bet_async(issue: int, room_id: int, amount: float, algo_used: Optional[str] = None):
    def worker():
        console.print(f"[cyan]Đang đặt {amount} BUILD -> PHÒNG_{room_id} (v{issue}) — Thuật toán: {algo_used}[/]")
        time.sleep(random.uniform(0.05, 0.45))
        res = place_bet_http(issue, room_id, amount)
        rec = record_bet(issue, room_id, amount, res, algo_used=algo_used)
        if isinstance(res, dict) and (res.get("msg") == "ok" or res.get("code") == 0 or res.get("status") in ("ok", 1)):
            bet_sent_for_issue.add(issue)
            console.print(f"[green]✅ Đặt thành công {amount} BUILD vào PHÒNG_{room_id} (v{issue}).[/]")
        else:
            console.print(f"[red]❌ Đặt lỗi v{issue}: {res}[/]")
    threading.Thread(target=worker, daemon=True).start()

def lock_prediction_if_needed(force: bool = False):
    global prediction_locked, predicted_room, ui_state, current_bet, _rounds_placed_since_skip, skip_next_round_flag, _skip_rounds_remaining, stop_flag

    if stop_flag:
        return
    if prediction_locked and not force:
        return
    if issue_id is None:
        return

    # --- Refactored Logic for Robustness ---

    # 1. Make a prediction first.
    mode = settings.get("algo", "RANDOM")
    chosen, algo_used = choose_room_tn(mode)

    # 2. Set prediction and lock UI. This ensures the user sees the prediction.
    predicted_room = chosen
    prediction_locked = True
    ui_state = "PREDICTED"

    # 3. Check for skip conditions. If skipping, we show the prediction but don't bet.
    if _skip_rounds_remaining > 0:
        console.print(f"[yellow]⏸️ Đang nghỉ { _skip_rounds_remaining } ván theo cấu hình sau khi thua.[/]")
        _skip_rounds_remaining -= 1
        return

    if skip_next_round_flag:
        console.print("[yellow]⏸️ TẠM DỪNG THEO DÕI SÁT THỦ[/]")
        skip_next_round_flag = False
        return

    # 4. If in AUTO mode, proceed to bet.
    if run_mode == "AUTO":
        # Use the globally updated balance from the BalancePoller thread to avoid blocking.
        bld = current_build
        if bld is None:
            # Fallback for the first run if poller hasn't run yet.
            bld, _, _ = fetch_balances_3games(retries=1, timeout=3)
            if bld is None:
                console.print("[yellow]⚠️ Không lấy được số dư, không thể đặt cược. Sẽ thử lại...[/]")
                prediction_locked = False  # UNLOCK to allow retry
                ui_state = "ANALYZING"      # Revert UI state
                return

        if current_bet is None:
            current_bet = base_bet
        amt = float(current_bet)

        if amt <= 0:
            console.print("[yellow]⚠️ Số tiền đặt không hợp lệ (<=0). Bỏ qua.[/]")
            return

        # CRITICAL FIX: Check if balance is sufficient for the Martingale bet.
        if amt > bld:
            console.print(f"[red]🔥 VỐN KHÔNG ĐỦ ĐỂ GẤP THẾP! Cần {amt:,.2f} nhưng chỉ có {bld:,.2f}. Reset về cược gốc.[/red]")
            current_bet = base_bet
            amt = float(current_bet)
            if amt > bld:
                console.print(f"[red]💀 Vốn không đủ để đặt cược gốc ({amt:,.2f}). Dừng tool.[/red]")
                stop_flag = True
                return

        place_bet_async(issue_id, predicted_room, amt, algo_used=algo_used)
        _rounds_placed_since_skip += 1
        if bet_rounds_before_skip > 0 and _rounds_placed_since_skip >= bet_rounds_before_skip:
            skip_next_round_flag = True
            _rounds_placed_since_skip = 0

def safe_send_enter_game(ws):
    if not ws:
        log_debug("safe_send_enter_game: ws None")
        return
    try:
        payload = {"msg_type": "handle_enter_game", "asset_type": "BUILD", "user_id": USER_ID, "user_secret_key": SECRET_KEY}
        ws.send(json.dumps(payload))
        log_debug("Sent enter_game")
    except Exception as e:
        log_debug(f"safe_send_enter_game err: {e}")

def _extract_issue_id(d: Dict[str, Any]) -> Optional[int]:
    if not isinstance(d, dict):
        return None
    possible = []
    for key in ("issue_id", "issueId", "issue", "id"):
        v = d.get(key)
        if v is not None:
            possible.append(v)
    if isinstance(d.get("data"), dict):
        for key in ("issue_id", "issueId", "issue", "id"):
            v = d["data"].get(key)
            if v is not None:
                possible.append(v)
    for p in possible:
        try:
            return int(p)
        except Exception:
            try:
                return int(str(p))
            except Exception:
                continue
    return None

def on_open(ws):
    _ws["ws"] = ws
    console.print("[green]ĐANG TRUY CẬP DỮ LIỆU GAME[/]")
    safe_send_enter_game(ws)

def on_message(ws, message):
    global issue_id, count_down, killed_room, round_index, ui_state, analysis_start_ts, issue_start_ts
    global issue_end_ts
    global prediction_locked, predicted_room, last_killed_room, last_msg_ts, current_bet
    global win_streak, lose_streak, max_win_streak, max_lose_streak, cumulative_profit, _skip_rounds_remaining, stop_flag
    last_msg_ts = time.time()
    try:
        if isinstance(message, bytes):
            try:
                message = message.decode("utf-8", errors="replace")
            except Exception:
                message = str(message)
        data = None
        try:
            data = json.loads(message)
        except Exception:
            try:
                data = json.loads(message.replace("'", '"'))
            except Exception:
                log_debug(f"on_message non-json: {str(message)[:200]}")
                return

        if isinstance(data, dict) and isinstance(data.get("data"), str):
            try:
                inner = json.loads(data.get("data"))
                merged = dict(data)
                merged.update(inner)
                data = merged
            except Exception:
                pass

        msg_type = data.get("msg_type") or data.get("type") or ""
        msg_type = str(msg_type)
        new_issue = _extract_issue_id(data)
        
        if msg_type == "notify_enter_game":
            info = data.get("info", {})
            if isinstance(info, dict):
                if info.get("start_time"):
                    st = float(info.get("start_time"))
                    if st > time.time() * 500: st /= 1000.0
                    issue_start_ts = st
                if info.get("end_time"):
                    et = float(info.get("end_time"))
                    if et > time.time() * 500: et /= 1000.0
                    issue_end_ts = et
            if data.get("last_killed_room_id"):
                last_killed_room = int(data["last_killed_room_id"])
            room_stat = data.get("room_stat", [])
            if isinstance(room_stat, list):
                for rm in room_stat:
                    _process_room_update(rm)
        if msg_type == "notify_issue_stat" or "issue_stat" in msg_type:
            rooms = data.get("rooms") or []
            if not rooms and isinstance(data.get("data"), dict):
                rooms = data["data"].get("rooms", [])
            for rm in (rooms or []):
                _process_room_update(rm)
                try:
                    rid = int(rm.get("room_id") or rm.get("roomId") or rm.get("id"))
                except Exception:
                    continue
                players = int(rm.get("user_cnt") or rm.get("userCount") or 0) or 0
                bet = int(rm.get("total_bet_amount") or rm.get("totalBet") or rm.get("bet") or 0) or 0
                room_state[rid] = {"players": players, "bet": bet}
                room_stats[rid]["last_players"] = players
                room_stats[rid]["last_bet"] = bet
            if new_issue is not None and new_issue != issue_id:
                log_debug(f"New issue: {issue_id} -> {new_issue}")
                issue_id = new_issue
                if data.get("start_time"):
                    st = float(data.get("start_time"))
                    if st > time.time() * 500: st /= 1000.0
                    issue_start_ts = st
                else:
                    issue_start_ts = time.time()
                issue_end_ts = issue_start_ts + 60.0 # Fallback
                round_index += 1
                killed_room = None
                prediction_locked = False
                predicted_room = None
                ui_state = "ANALYZING"
                analysis_start_ts = time.time()

        elif msg_type == "notify_count_down" or "count_down" in msg_type:
            count_down = data.get("count_down") or data.get("countDown") or data.get("count") or count_down
            try:
                count_val = int(count_down)
            except Exception:
                count_val = None
            if count_val is not None and count_val <= 10 and not prediction_locked:
                lock_prediction_if_needed()

        elif msg_type == "notify_result" or "result" in msg_type:
            kr = None
            possible_keys = ["killed_room", "killed_room_id", "killedRoom", "killedRoomId", "kill_room"]
            for key in possible_keys:
                if data.get(key) is not None:
                    kr = data.get(key)
                    break
            if kr is None and isinstance(data.get("data"), dict):
                for key in possible_keys:
                    if data["data"].get(key) is not None:
                        kr = data["data"].get(key)
                        break
            if kr is not None:
                try:
                    krid = int(kr)
                except Exception:
                    krid = kr
                killed_room = krid
                game_kill_log.append(krid)
                update_killer_history(krid)
                last_killed_room = krid
                for rid in ROOM_ORDER:
                    if rid == krid:
                        room_stats[rid]["kills"] += 1
                        room_stats[rid]["last_kill_round"] = round_index
                    else:
                        room_stats[rid]["survives"] += 1

                balance_before_payout = current_build
                rec = None
                for b in reversed(bet_history):
                    if b.get("issue") == issue_id:
                        rec = b
                        break
                if rec is not None:
                    try:
                        placed_room = int(rec.get("room"))
                        if placed_room != int(killed_room):
                            rec["result"] = "Thắng"
                            current_bet = base_bet
                            win_streak += 1
                            lose_streak = 0
                            if win_streak > max_win_streak:
                                max_win_streak = win_streak
                        else:
                            rec["result"] = "Thua"
                            try:
                                # On loss, multiply the bet amount for the next round.
                                # The value of `current_bet` at this point is the amount that was just lost.
                                if current_bet is not None:
                                    current_bet *= float(multiplier)
                            except Exception:
                                current_bet = base_bet
                            lose_streak += 1
                            win_streak = 0
                            if lose_streak > max_lose_streak:
                                max_lose_streak = lose_streak
                            if pause_after_losses > 0:
                                _skip_rounds_remaining = pause_after_losses

                        # Trigger background balance fetch and delta calculation
                        threading.Thread(
                            target=_background_update_balance_after_result,
                            args=(rec, balance_before_payout),
                            daemon=True
                        ).start()
                        rec["win_streak"] = win_streak
                        rec["lose_streak"] = lose_streak
                    except Exception as e:
                        log_debug(f"result handle err: {e}")
            ui_state = "RESULT"

            try:
                if stop_when_profit_reached and profit_target is not None and isinstance(current_build, (int, float)) and current_build >= profit_target and not stop_flag:
                    console.print(f"[bold green]🎉 MỤC TIÊU LÃI ĐẠT: {current_build} >= {profit_target}. Dừng tool.[/]")
                    stop_flag = True
                    try:
                        wsobj = _ws.get("ws")
                        if wsobj:
                            wsobj.close()
                    except Exception:
                        pass
                if stop_when_loss_reached and stop_loss_target is not None and isinstance(current_build, (int, float)) and current_build <= stop_loss_target and not stop_flag:
                    console.print(f"[bold red]💀 CẮT LỖ: {current_build:,.2f} <= {stop_loss_target:,.2f}. Dừng tool.[/]")
                    stop_flag = True
                    try:
                        wsobj = _ws.get("ws")
                        if wsobj:
                            wsobj.close()
                    except Exception:
                        pass
            except Exception:
                pass

    except Exception as e:
        log_debug(f"on_message err: {e}")

def _background_update_balance_after_result(rec: dict, balance_before: Optional[float]):
    """Fetches balance and calculates profit/loss for a specific bet record."""
    global cumulative_profit
    try:
        # Wait a bit for backend to update
        time.sleep(2.5)
        new_balance, _, _ = fetch_balances_3games(retries=2, timeout=5)

        if rec and isinstance(new_balance, (int, float)):
            # If we have a balance from before the result, use that for a more accurate delta
            if isinstance(balance_before, (int, float)):
                delta = new_balance - balance_before
                rec['delta'] = delta
            else:
                # Fallback if we didn't have a good 'before' balance
                if rec.get('result') == 'Thắng':
                    rec['delta'] = float(rec.get('amount', 0)) * 7
                elif rec.get('result') == 'Thua':
                    rec['delta'] = -float(rec.get('amount', 0))
    except Exception as e:
        log_debug(f"Error in background balance update: {e}")

def update_killer_history(killed_room_id):
    """Cập nhật lịch sử của sát thủ."""
    if killed_room_id in room_state:
        killer_history.append({
            'players': room_state[killed_room_id].get('players', 0),
            'bet': room_state[killed_room_id].get('bet', 0)
        })

def _process_room_update(room_data: dict):
    if not isinstance(room_data, dict):
        return
    try:
        rid = int(room_data.get("room_id") or room_data.get("roomId") or room_data.get("id"))
        players = int(room_data.get("user_cnt") or room_data.get("userCount") or 0) or 0
        bet = _parse_number(room_data.get("total_bet_amount") or room_data.get("totalBet") or room_data.get("bet") or 0) or 0
        room_state[rid] = {"players": players, "bet": bet}
        room_stats[rid]["last_players"] = players
        room_stats[rid]["last_bet"] = bet
    except (ValueError, TypeError):
        pass

def on_close(ws, code, reason):
    log_debug(f"WS closed: {code} {reason}")

def on_error(ws, err):
    log_debug(f"WS error: {err}")

def start_ws():
    backoff = 1.0
    while not stop_flag:
        try:
            ws_app = websocket.WebSocketApp(WS_URL, on_open=on_open, on_message=on_message, on_close=on_close, on_error=on_error)
            _ws["ws"] = ws_app
            ws_app.run_forever(ping_interval=15, ping_timeout=6)
        except Exception as e:
            log_debug(f"start_ws exception: {e}")
        t = min(backoff + random.random() * 0.8, 30)
        log_debug(f"Reconnect WS after {t}s")
        time.sleep(t)
        backoff = min(backoff * 1.8, 30)

class BalancePoller(threading.Thread):
    def __init__(self, uid: Optional[int], secret: Optional[str], poll_seconds: int = 2, on_balance=None, on_error=None, on_status=None):
        super().__init__(daemon=True)
        self.uid = uid
        self.secret = secret
        self.poll_seconds = max(1, int(poll_seconds))
        self._running = True
        self._last_balance_local: Optional[float] = None
        self.on_balance = on_balance
        self.on_error = on_error
        self.on_status = on_status

    def stop(self):
        self._running = False

    def run(self):
        if self.on_status:
            self.on_status("Kết nối...")
        while self._running and not stop_flag:
            try:
                build, world, usdt = fetch_balances_3games(params={"userId": str(self.uid)} if self.uid else None, uid=self.uid, secret=self.secret)
                if build is None:
                    raise RuntimeError("Không đọc được balance từ response")
                delta = 0.0 if self._last_balance_local is None else (build - self._last_balance_local)
                first_time = (self._last_balance_local is None)
                if first_time or abs(delta) > 0:
                    self._last_balance_local = build
                    if self.on_balance:
                        self.on_balance(float(build), float(delta), {"ts": human_ts()})
                    if self.on_status:
                        self.on_status("Đang theo dõi")
                else:
                    if self.on_status:
                        self.on_status("Đang theo dõi (không đổi)")
            except Exception as e:
                if self.on_error:
                    self.on_error(str(e))
                if self.on_status:
                    self.on_status("Lỗi kết nối (thử lại...)")
            for _ in range(max(1, int(self.poll_seconds * 5))):
                if not self._running or stop_flag:
                    break
                time.sleep(0.2)
        if self.on_status:
            self.on_status("Đã dừng")

def monitor_loop():
    global last_balance_fetch_ts, last_msg_ts, stop_flag
    while not stop_flag:
        now = time.time()
        if now - last_balance_fetch_ts >= BALANCE_POLL_INTERVAL:
            last_balance_fetch_ts = now
            try:
                fetch_balances_3games(params={"userId": str(USER_ID)} if USER_ID else None)
            except Exception as e:
                log_debug(f"monitor fetch err: {e}")
        if now - last_msg_ts > 12:
            log_debug("No ws msg >12s, send enter_game")
            try:
                safe_send_enter_game(_ws.get("ws"))
            except Exception as e:
                log_debug(f"monitor send err: {e}")
        if now - last_msg_ts > 45:
            log_debug("No ws msg >45s, force reconnect")
            try:
                wsobj = _ws.get("ws")
                if wsobj:
                    try:
                        wsobj.close()
                    except Exception:
                        pass
            except Exception:
                pass
        try:
            if analysis_start_ts and (time.time() - analysis_start_ts >= analysis_duration) and not prediction_locked:
                lock_prediction_if_needed()
        except Exception:
            pass
        time.sleep(0.6)

def _spinner_char():
    return _spinner[int(time.time() * 4) % len(_spinner)]

def _rainbow_border_style() -> str:
    idx = int(time.time() * 4) % len(VIP_COLORS)
    return VIP_COLORS[idx]

def build_header(border_color: Optional[str] = None):
    border_style = border_color or _rainbow_border_style()

    info_table = Table(box=None, show_header=False, pad_edge=False, expand=True)
    info_table.add_column(style="bold cyan", no_wrap=True, justify="right", width=16)
    info_table.add_column(style="white")

    info_table.add_row("👤 Tài khoản:", f"[bold white]{USER_ID}[/bold white]" if USER_ID else "-")

    b = f"{current_build:,.2f}" if isinstance(current_build, (int, float)) else "-"
    u = f"{current_usdt:,.2f}" if isinstance(current_usdt, (int, float)) else "-"
    w = f"{current_world:,.2f}" if isinstance(current_world, (int, float)) else "-"
    balance_text = Text.assemble(
        (f"{u} ", "bold yellow"), ("USDT", "dim yellow"),
        (" | ", "dim"),
        (f"{w} ", "bold green"), ("XWRLD", "dim green"),
        (" | ", "dim"),
        (f"{b} ", "bold cyan"), ("BUILD", "dim cyan"),
    )
    info_table.add_row("💰 Số dư:", balance_text)

    pnl_val = cumulative_profit if cumulative_profit is not None else 0
    pnl_str = f"{pnl_val:+,.2f} BUILD"
    pnl_style = "bold green" if pnl_val > 0 else ("bold red" if pnl_val < 0 else "bold yellow")
    info_table.add_row("📈 Lãi/Lỗ:", Text(pnl_str, style=pnl_style))

    info_table.add_row("🕹️ Tổng ván:", f"[bold white]{round_index}[/bold white] (Ván hiện tại: {issue_id or '-'})")

    current_streak_text = Text.assemble(
        ("�", "green"), (f" {win_streak}", "bold white"),
        (" | ", "dim"),
        ("🧊", "red"), (f" {lose_streak}", "bold white")
    )
    info_table.add_row("📊 Chuỗi hiện tại:", current_streak_text)

    max_streak_text = Text.assemble(
        ("🏆", "yellow"), (f" {max_win_streak}", "bold white"),
        (" | ", "dim"),
        ("💀", "red"), (f" {max_lose_streak}", "bold white")
    )
    info_table.add_row("⭐ Chuỗi K.Lục:", max_streak_text)

    algo_label = SELECTION_MODES.get(settings.get('algo'), settings.get('algo'))
    info_table.add_row("⚙️ Thuật toán:", Text(algo_label, style="bold magenta"))

    now_str = datetime.now(tz).strftime("%Y-%m-%d %H:%M:%S")
    subtitle = Text(f"by Nguyen  •  {now_str}", style="dim", justify="center")
    final_group = Group(info_table, subtitle)
    return Panel(final_group, title="[bold magenta]⚡ VUA THOÁT HIỂM VIP ⚡[/]", border_style=border_style, padding=(1, 2), expand=True)

MARQUEE_MESSAGES = [
    "⚡ Vua Thoát Hiểm VIP BY TNTOOL - Chúc bạn may mắn! ⚡",
    "🧠 AI đang phân tích dữ liệu và đưa ra kết quả an toàn cho bạn",
    "💰 Không tham , chơi không theo cảm xúc hãy chơi vì chính mình.",
    "🏆 Chiến thắng không kiêu, bại không nản !!",
    "🤖 Tôi là AI tôi sẽ giúp bạn làm giàu",
    "❄️ Cái đầu lạnh giúp bạn chiến thắng",
]

def build_marquee():
    message = MARQUEE_MESSAGES[int(time.time() / 10) % len(MARQUEE_MESSAGES)]
    full_text = " " * 20 + message + " " * 20
    width = console.width or 80
    start_index = int(time.time() * 2) % len(full_text)
    display_text = (full_text * 3)[start_index : start_index + width]
    return Panel(Text(display_text, style="bold #00AFFF", no_wrap=True), box=box.ROUNDED, border_style="dim", padding=0, expand=True)

def build_rooms_grid(border_color: Optional[str] = None):
    """Xây dựng giao diện lưới các phòng chơi theo phong cách dashboard."""
    room_panels = []
    for r in ROOM_ORDER:
        st = room_state.get(r, {})
        players = st.get("players", 0)
        bet_val = st.get('bet', 0) or 0
        bet_fmt = f"{int(bet_val):,}"

        is_predicted = predicted_room is not None and int(r) == int(predicted_room)
        is_killed = killed_room is not None and int(r) == int(killed_room)

        panel_border_style = "dim"
        title_style = "white"
        content_style = "default"

        if is_killed and is_predicted:
            panel_border_style = "bold red"
            title_style = "bold red"
            content_style = "on #400000"
        elif is_killed:
            panel_border_style = "red"
            title_style = "red"
        elif is_predicted:
            panel_border_style = "bold green"
            title_style = "bold green"

        content = Text.assemble(
            (f"\n", "default"),
            (f"👥 {players}\n", "default"),
            (f"💰 {bet_fmt}", "yellow"),
            (f"\n", "default"),
            justify="center"
        )

        room_panel = Panel(
            Align.center(content, vertical="middle"),
            title=f"[{title_style}]{ROOM_NAMES.get(r, f'Phòng {r}')}[/]",
            border_style=panel_border_style,
            box=box.HEAVY,
            expand=True,
            height=7,
            style=content_style
        )
        room_panels.append(room_panel)

    main_panel = Panel(
        Columns(room_panels, equal=True, expand=True),
        title="[bold green]🕹️ BÀN CHƠI[/bold green]",
        box=box.HEAVY,
        border_style=(border_color or _rainbow_border_style()),
        expand=True
    )
    return main_panel

_ANALYSIS_STEPS = [
    "Quét dữ liệu lịch sử...",
    "Đánh giá rủi ro các phòng...",
    "Phân tích hành vi người chơi...",
    "Tính toán xác suất bị tiêu diệt...",
    "Mô phỏng các kết quả có thể xảy ra...",
    "Xác định phòng an toàn nhất...",
]
def build_mid(border_color: Optional[str] = None):
    global analysis_start_ts
    if ui_state == "ANALYZING":
        now = time.time()
        elapsed = now - (analysis_start_ts or now)
        progress = min(1.0, elapsed / analysis_duration)

        title_time_str = ""
        if issue_end_ts and now < issue_end_ts:
            remaining_s = int(issue_end_ts - now)
            title_time_str = f"⏳ Còn: {remaining_s}s"
            if remaining_s < 10:
                 title_time_str = f"[blink bold red]⏳ Còn: {remaining_s}s[/]"
        else:
            title_time_str = f"{(progress*100):.0f}%"

        lines = []

        bar_width = 20
        filled_len = int(bar_width * progress)
        bar = '█' * filled_len + '─' * (bar_width - filled_len)
        lines.append(f"[bold cyan]Phân tích: [{bar}] {(progress*100):.0f}%[/bold cyan]")
        lines.append("")

        num_steps = len(_ANALYSIS_STEPS)
        for i, step_text in enumerate(_ANALYSIS_STEPS):
            step_progress = (i + 1) / num_steps
            if progress >= step_progress:
                lines.append(f"[green]✅[/green] {step_text}")
            elif progress > i / num_steps:
                lines.append(f"[yellow]{_spinner_char()}[/yellow] {step_text}")
            else:
                lines.append(f"[dim]◻️ {step_text}[/dim]")

        txt = "\n".join(lines)
        title = f"[bold]🧠 AI ĐANG PHÂN TÍCH[/bold] | {Text.from_markup(title_time_str)}"
        return Panel(Text.from_markup(txt), title=title, box=box.HEAVY, border_style=(border_color or _rainbow_border_style()), padding=(1,2), expand=True)

    elif ui_state == "PREDICTED":
        name = ROOM_NAMES.get(predicted_room, f"Phòng {predicted_room}") if predicted_room else '-'
        last_bet_amt_str = f"{current_bet:,.2f}" if current_bet is not None else '-'
        now = time.time()
        title_text = Text.assemble(("[bold]🔮 DỰ ĐOÁN[/bold]", "default"))
        if issue_end_ts and now < issue_end_ts:
            remaining_s = int(issue_end_ts - now)
            title_text.append(f" | ⏳ Chốt sau: {remaining_s}s")

        prediction_panel = Panel(
            Align.center(Text(name, style="bold white"), vertical="middle"),
            title="[bold green]🎯 PHÒNG AN TOÀN[/bold green]",
            border_style="green",
            box=box.DOUBLE,
            height=5
        )

        bet_panel = Panel(
            Text.assemble(
                ("💰 Đặt: ", "default"),
                (f"{last_bet_amt_str}", "bold yellow"),
                (" BUILD", "yellow")
            ),
            title="[bold]Mức cược[/bold]"
        )

        info_text = Text.from_markup(f"""☠️ Ván trước: {ROOM_NAMES.get(last_killed_room, '-')}
📈 Thắng: {win_streak} | 📉 Thua: {lose_streak}""")

        content = Group(
            Align.center(prediction_panel),
            Align.center(bet_panel),
            Align.center(info_text),
            Align.center(Text(f"Chờ kết quả... {_spinner_char()}"))
        )

        return Panel(content, title=title_text, box=box.HEAVY, border_style=(border_color or _rainbow_border_style()), padding=1, expand=True)

    elif ui_state == "RESULT":
        k = ROOM_NAMES.get(killed_room, "-") if killed_room else "-"

        last_bet = None
        if bet_history:
            last_bet = bet_history[-1]

        result_text = ""
        result_style = ""
        border = "yellow"

        if last_bet and last_bet.get('issue') == issue_id:
            if last_bet.get('result') == "Thắng":
                result_text = "THẮNG"
                result_style = "bold white on green"
                border = "green"
            elif last_bet.get('result') == "Thua":
                result_text = "THUA"
                result_style = "bold white on red"
                border = "red"

        if not result_text:
            result_text = "CHỜ"
            result_style = "bold white on blue"
            border = "blue"

        result_panel = Panel(
            Align.center(Text(result_text, style=result_style, justify="center"), vertical="middle"),
            height=5,
            border_style=border
        )

        lines = []
        lines.append(f"☠️ Sát thủ đã vào: [bold red]{k}[/bold red]")

        pnl_val = cumulative_profit if cumulative_profit is not None else 0
        pnl_str = f"{pnl_val:+,.4f} BUILD"
        title_text = Text.assemble(("[bold]📊 KẾT QUẢ[/bold]", "default"))
        if count_down is not None:
            title_text.append(Text.from_markup(f" | ⏳ Chờ ván mới: [bold]{count_down}s[/bold]"))
        pnl_style = "green" if pnl_val > 0 else ("red" if pnl_val < 0 else "yellow")
        lines.append(f"📈 Tổng Lãi/lỗ: [{pnl_style} bold]{pnl_str}[/{pnl_style} bold]")

        if last_bet and last_bet.get('issue') == issue_id:
            delta = last_bet.get('delta', 0.0)
            delta_str = f"{delta:+,.4f} BUILD"
            delta_style = "green" if delta > 0 else ("red" if delta < 0 else "yellow")
            lines.append(f"💸 Ván này: [{delta_style}]{delta_str}[/{delta_style}]")

        info_text = Text.from_markup("\n".join(lines))

        content = Group(
            result_panel,
            Align.center(info_text)
        )

        return Panel(content, title=title_text, box=box.HEAVY, border_style=(border_color or _rainbow_border_style()), padding=1, expand=True)
    else:
        lines = []
        time_remaining_str = ""
        if issue_end_ts and time.time() < issue_end_ts:
            remaining_s = int(issue_end_ts - time.time())
            time_remaining_str = f"⏳ Ván kết thúc sau: [bold]{remaining_s}s[/bold]"
        elif count_down is not None:
             time_remaining_str = f"⏳ Bắt đầu sau: [bold]{count_down}s[/bold]"
        else:
            time_remaining_str = "Đang chờ ván mới..."
        lines.append(time_remaining_str)
        lines.append(f"🎯 Dự đoán trước: {ROOM_NAMES.get(predicted_room, '-') if predicted_room else '-'}")
        txt = "\n".join(lines)
        return Panel(Align.center(Text.from_markup(txt), vertical="middle"), title="[bold green]TRẠNG THÁI[/bold green]", box=box.HEAVY, border_style=(border_color or _rainbow_border_style()), expand=True)

def build_bet_table(border_color: Optional[str] = None):
    t = Table(title="Lịch sử cược", box=box.ROUNDED, expand=True, border_style="dim")
    t.add_column("Ván", no_wrap=True, style="dim")
    t.add_column("Phòng", no_wrap=True, style="cyan")
    t.add_column("Tiền", justify="right", no_wrap=True, style="yellow")
    t.add_column("KQ", no_wrap=True)
    t.add_column("Thuật toán", no_wrap=True, style="magenta")
    last_n = list(bet_history)[-7:]
    for b in reversed(last_n):
        amt = b.get('amount') or 0
        amt_fmt = f"{float(amt):,.2f}"
        res = str(b.get('result') or 'Đang')
        algo = str(b.get('algo') or '-')
        if res.lower().startswith('thắng'):
            res_text = Text("✅ Thắng", style="green")
            row_style = ""
        elif res.lower().startswith('thua'):
            res_text = Text("❌ Thua", style="red")
            row_style = "dim"
        else:
            res_text = Text("⏳ Đang", style="yellow")
            row_style = ""
        t.add_row(str(b.get('issue') or '-'), ROOM_NAMES.get(b.get('room'), str(b.get('room') or '-')), amt_fmt, res_text, algo, style=row_style)
    return Panel(t, title="[bold cyan]📜 LỊCH SỬ GIAO DỊCH[/bold cyan]", box=box.HEAVY, border_style=(border_color or _rainbow_border_style()), expand=True)

STRATEGY_CONFIG_FILE = "strategy_vth.json"

def save_strategy_config():
    """Lưu cấu hình chiến lược hiện tại vào file."""
    config_data = {
        "base_bet": base_bet,
        "multiplier": multiplier,
        "algo": settings.get("algo"),
        "bet_rounds_before_skip": bet_rounds_before_skip,
        "pause_after_losses": pause_after_losses,
        "profit_target": profit_target,
        "stop_when_profit_reached": stop_when_profit_reached,
        "stop_loss_target": stop_loss_target,
        "stop_when_loss_reached": stop_when_loss_reached,
    }
    try:
        with open(STRATEGY_CONFIG_FILE, "w", encoding="utf-8") as f:
            json.dump(config_data, f, indent=2)
    except Exception as e:
        console.print(f"[red]❌ Lỗi khi lưu cấu hình: {e}[/red]")

def load_strategy_config() -> bool:
    """Tải cấu hình chiến lược từ file."""
    global base_bet, multiplier, run_mode, bet_rounds_before_skip, current_bet, pause_after_losses, profit_target, stop_when_profit_reached, stop_loss_target, stop_when_loss_reached
    
    if not Path(STRATEGY_CONFIG_FILE).exists():
        console.print(f"[yellow]⚠️ Không tìm thấy file cấu hình '{STRATEGY_CONFIG_FILE}'. Vui lòng dùng tùy chọn 'Cài cấu hình' trước.[/yellow]")
        return False
        
    try:
        with open(STRATEGY_CONFIG_FILE, "r", encoding="utf-8") as f:
            config_data = json.load(f)
        
        base_bet = config_data.get("base_bet", 1.0)
        multiplier = config_data.get("multiplier", 2.0)
        settings["algo"] = config_data.get("algo", "SAFE")
        bet_rounds_before_skip = config_data.get("bet_rounds_before_skip", 0)
        pause_after_losses = config_data.get("pause_after_losses", 0)
        profit_target = config_data.get("profit_target", None)
        stop_when_profit_reached = config_data.get("stop_when_profit_reached", False)
        stop_loss_target = config_data.get("stop_loss_target", None)
        stop_when_loss_reached = config_data.get("stop_when_loss_reached", False)
        current_bet = base_bet
        run_mode = "AUTO"
        
        console.print(f"[green]✅ Đã tải cấu hình chiến lược từ '{STRATEGY_CONFIG_FILE}'[/green]")
        summary = Table(box=box.ROUNDED, show_header=False, border_style="green")
        summary.add_column(style="bold cyan")
        summary.add_column(style="white")
        summary.add_row("💰 Cược gốc:", f"{base_bet:,.2f} BUILD")
        summary.add_row("📈 Hệ số nhân:", f"x{multiplier}")
        summary.add_row("🧠 Thuật toán:", f"{SELECTION_MODES.get(settings['algo'])}")
        summary.add_row("🛡️ Chống soi:", f"Nghỉ 1 ván sau {bet_rounds_before_skip} ván" if bet_rounds_before_skip > 0 else "Không kích hoạt")
        summary.add_row("⏸️ Nghỉ khi thua:", f"Nghỉ {pause_after_losses} ván" if pause_after_losses > 0 else "Không kích hoạt")
        summary.add_row("🎯 Mục tiêu lãi:", f"Dừng khi đạt {profit_target:,.2f} BUILD" if profit_target else "Chạy vô hạn")
        summary.add_row("💀 Cắt lỗ:", f"Dừng khi còn {stop_loss_target:,.2f} BUILD" if stop_loss_target else "Không kích hoạt")
        console.print(Panel(summary, title="[bold]CẤU HÌNH ĐÃ TẢI[/bold]", box=box.HEAVY, border_style="green", expand=False))
        time.sleep(2)
        return True
    except Exception as e:
        console.print(f"[red]❌ Lỗi khi tải cấu hình: {e}[/red]")
        return False

def prompt_settings() -> bool:
    """Hiển thị màn hình cài đặt cho người dùng. Trả về True nếu người dùng xác nhận, False nếu hủy."""
    global base_bet, multiplier, run_mode, bet_rounds_before_skip, current_bet, pause_after_losses, profit_target, stop_when_profit_reached, stop_loss_target, stop_when_loss_reached
    console.clear()
    console.print(Panel(Text("🚀 THIẾP LẬP CẤU HÌNH 🚀", justify="center", style="bold magenta"), box=box.DOUBLE, border_style="magenta"))
    console.print("\n[cyan]Hãy thiết tập cách chơi của bạn [/cyan]")
    console.print(Rule("[bold #AF00FF]BƯỚC 1: QUẢN LÝ VỐN[/]", style="#AF00FF"))
    slow_print("hôm nay liều hay lãi an toàn hãy suy nghĩ cho kỹ nhoa:3 ", style="dim")
    base_bet = FloatPrompt.ask("   [1] 💰 Nhập số BUILD chơi mỗi ván (thấp nhất: 1.0)", default=1.0)
    multiplier = FloatPrompt.ask("   [2] 📈 Nhập hệ số nhân khi thua (gấp thếp, nên 10 trở lên)", default=2.0)
    current_bet = base_bet
    console.print(Rule("[bold #5F00FF]BƯỚC 2: LỰA CHỌN CÁCH CHƠI AN TOÀN CỦA BẠN[/]", style="#5F00FF"))
    slow_print("CÁC LOGIC ĐÃ THỬ VÀ TRẢI NGHIỆM ĐÃ AN TOÀN", style="dim")
    modes = list(SELECTION_MODES.items())
    for i, (k, label) in enumerate(modes, start=1):
        console.print(f"      [cyan]{label}[/]")
    choice = IntPrompt.ask("   [3] 🧠 HEHE BẠN ĐÃ CHỌN LOGIC", choices=[str(i) for i in range(1, len(modes) + 1)], default=1)
    settings["algo"] = modes[choice - 1][0]
    console.print(Rule("[bold #005FFF]BƯỚC 3: THÊM GIẢM RỦI RO KHÔNG NÈ?[/]", style="#005FFF"))
    slow_print("Các tính năng tùy chọn để quản lý rủi ro.", style="dim")
    bet_rounds_before_skip = IntPrompt.ask("   [4] 🛡️ Chống soi: Nghỉ 1 ván sau bao nhiêu ván đặt? (nhập 0 để bỏ qua)", default=0)
    pause_after_losses = IntPrompt.ask("   [5] ⏸️ Chống thua liên tiếp: Nghỉ bao nhiêu ván sau khi thua? (nhập 0 để bỏ qua)", default=0)
    pt_str = Prompt.ask("   [6] 🎯 Đặt mục tiêu lãi (nhập số dư đến đó sẽ dừng). [dim]Để trống để chạy vô hạn[/dim]", default="")
    if pt_str.strip():
        try:
            profit_target = float(pt_str)
            stop_when_profit_reached = True
        except ValueError:
            profit_target = None
            stop_when_profit_reached = False
    else:
        profit_target = None
        stop_when_profit_reached = False

    sl_str = Prompt.ask("   [7] 💀 Đặt mục tiêu cắt lỗ (nhập số dư đến đó sẽ dừng). [dim]Để trống để chạy vô hạn[/dim]", default="")
    if sl_str.strip():
        try:
            stop_loss_target = float(sl_str)
            stop_when_loss_reached = True
        except ValueError:
            stop_loss_target = None
            stop_when_loss_reached = False
    else:
        stop_loss_target = None
        stop_when_loss_reached = False
    console.print(Rule("[bold green]TỔNG KẾT CÀI ĐẶT[/]", style="green"))
    summary = Table(box=box.ROUNDED, show_header=False, border_style="green")
    summary.add_column(style="bold cyan")
    summary.add_column(style="white")
    summary.add_row("💰 Cược gốc:", f"{base_bet:,.2f} BUILD")
    summary.add_row("📈 Hệ số nhân:", f"x{multiplier}")
    summary.add_row("🧠 Thuật toán:", f"{SELECTION_MODES.get(settings['algo'])}")
    summary.add_row("🛡️ Chống soi:", f"Nghỉ 1 ván sau {bet_rounds_before_skip} ván" if bet_rounds_before_skip > 0 else "Không kích hoạt")
    summary.add_row("⏸️ Nghỉ khi thua:", f"Nghỉ {pause_after_losses} ván" if pause_after_losses > 0 else "Không kích hoạt")
    summary.add_row("🎯 Mục tiêu lãi:", f"Dừng khi đạt {profit_target:,.2f} BUILD" if profit_target else "Chạy vô hạn")
    summary.add_row("💀 Cắt lỗ:", f"Dừng khi còn {stop_loss_target:,.2f} BUILD" if stop_loss_target else "Không kích hoạt")
    console.print(Panel(summary, title="[bold]CHIẾN LƯỢC CỦA BẠN[/bold]", box=box.HEAVY, border_style="green", expand=False))
    
    start_choice = Prompt.ask(f"\n[bold green]>> NHẤN ENTER ĐỂ BẮT ĐẦU CHIẾN LUÔN NHÉ!![/bold green]", default="ok")
    if start_choice.lower() == 'q':
        return False
    console.clear()
    run_mode = "AUTO"
    return True

def start_threads():
    """Khởi động các thread nền (websocket, monitor)."""
    threading.Thread(target=start_ws, daemon=True).start()
    threading.Thread(target=monitor_loop, daemon=True).start()

def load_accounts() -> list:
    acc_file = Path("accounts.json")
    if not acc_file.exists():
        return []
    try:
        return json.loads(acc_file.read_text())
    except (json.JSONDecodeError, IOError):
        return []

def save_accounts(accounts: list):
    acc_file = Path("accounts.json")
    with acc_file.open("w", encoding="utf-8") as f:
        json.dump(accounts, f, indent=2)

def add_new_account(accounts: list) -> bool:
    """Thêm một tài khoản mới vào danh sách."""
    console.print(Rule("[bold cyan]Thêm tài khoản mới[/]"))
    link = Prompt.ask("Dán link trò chơi vào đây")
    if not link:
        console.print("[yellow]Đã hủy.[/yellow]")
        return False
    try:
        parsed = urlparse(link)
        params = parse_qs(parsed.query)
        if 'userId' in params and 'secretKey' in params:
            uid = int(params.get('userId')[0])
            skey = params.get('secretKey', [None])[0]
            if any(acc.get('userId') == uid for acc in accounts):
                console.print(f"[yellow]⚠️ Tài khoản userId: {uid} đã tồn tại trong danh sách.[/yellow]")
                return False
            accounts.append({"userId": uid, "secretKey": skey})
            save_accounts(accounts)
            console.print(f"[green]✅ Đã thêm thành công tài khoản userId: {uid}[/green]")
            return True
        else:
            console.print("[red]Link không hợp lệ, thiếu `userId` hoặc `secretKey`.[/red]")
            return False
    except Exception as e:
        console.print(f"[red]Lỗi khi xử lý link: {e}[/red]")
        return False

def delete_account(accounts: list) -> bool:
    """Xóa một tài khoản khỏi danh sách."""
    if not accounts:
        console.print("[yellow]Không có tài khoản nào để xóa.[/yellow]")
        return False
    console.print(Rule("[bold red]Xóa tài khoản[/]"))
    for i, acc in enumerate(accounts, 1):
        console.print(f"  [cyan]{i}[/]. userId: {acc.get('userId')}")
    choice_str = Prompt.ask("Chọn số thứ tự tài khoản để xóa (hoặc nhấn Enter để hủy)")
    if not choice_str:
        console.print("[yellow]Đã hủy.[/yellow]")
        return False
    try:
        choice_idx = int(choice_str) - 1
        if 0 <= choice_idx < len(accounts):
            removed_acc = accounts.pop(choice_idx)
            save_accounts(accounts)
            console.print(f"[green]✅ Đã xóa thành công tài khoản userId: {removed_acc.get('userId')}[/green]")
            return True
        else:
            console.print("[red]Lựa chọn không hợp lệ.[/red]")
            return False
    except ValueError:
        console.print("[red]Vui lòng nhập một số.[/red]")
        return False

def select_account() -> bool: # Sửa đổi để phù hợp với menu mới
    """Hiển thị danh sách tài khoản và cho phép người dùng chọn. Trả về True nếu chọn thành công."""
    global USER_ID, SECRET_KEY
    while True:
        console.clear()
        border_style = _rainbow_border_style()
        console.print(Panel(Text("🔐 ĐĂNG NHẬP & CHỌN TÀI KHOẢN 🔐", justify="center", style="bold yellow"), box=box.DOUBLE, border_style=border_style))
        accounts = load_accounts()
        if not accounts:
            console.print("\n[yellow]Không tìm thấy tài khoản nào. Vui lòng dùng tùy chọn 'Thêm tài khoản' trước.[/yellow]")
            time.sleep(2)
            return False
        table = Table(title="[bold]Danh sách tài khoản[/bold]", box=box.HEAVY, border_style="cyan")
        table.add_column("STT", style="bold magenta")
        table.add_column("User ID", style="white")
        table.add_column("Số dư BUILD", justify="right", style="cyan")
        with console.status("[green]Đang truy vấn số dư...[/]", spinner="dots") as status:
            for i, acc in enumerate(accounts, 1):
                uid = acc.get('userId')
                skey = acc.get('secretKey')
                status.update(f"[green]Đang kiểm tra tài khoản {uid}...[/]")
                build, _, _ = fetch_balances_3games(uid=uid, secret=skey)
                balance_str = f"[bold green]{build:,.4f}[/bold green]" if build is not None else "[red]Không thể lấy[/red]"
                table.add_row(str(i), str(uid), balance_str)
        console.print(table)

        choices = [str(i) for i in range(1, len(accounts) + 1)]
        choice_str = Prompt.ask(f"chọn số thứ tự tài khoản: (1-{len(accounts)}) để chạy nhé", choices=choices, default="")
        
        if not choice_str:
            return False
        
        try:
            choice_idx = int(choice_str) - 1
            if 0 <= choice_idx < len(accounts):
                selected_account = accounts[choice_idx]
                USER_ID = selected_account['userId']
                SECRET_KEY = selected_account['secretKey']
                console.print(f"\n[bold green]✅ Đã chọn tài khoản: userId={USER_ID}[/bold green]")
                time.sleep(1.5)
                return True
            else:
                console.print("[red]Lựa chọn không hợp lệ.[/red]")
                time.sleep(1)
                return False
        except ValueError:
            console.print("[red]Lựa chọn không hợp lệ.[/red]")
            time.sleep(1)
            return False

def start_game_flow():
    """Encapsulates the logic to start the game (WS, balance poller, and live UI)."""
    global stop_flag # Allow this function to set stop_flag to exit the main loop

    if USER_ID is None or SECRET_KEY is None:
        console.print("[red]❌ Không có tài khoản được chọn. Vui lòng chọn tài khoản trước khi bắt đầu chơi.[/red]")
        time.sleep(2)
        return

    console.print(Rule("[bold green]HỆ THỐNG ĐANG KHỞI ĐỘNG...[/]", style="green"))
    start_threads()

    with console.status("[bold green]Đang kết nối với máy chủ game...[/]", spinner="dots") as status:
        initial_wait_start = time.time()
        while issue_id is None and (time.time() - initial_wait_start) < 30:
            time.sleep(0.5)
        if issue_id is None:
            console.print("\n[bold red]❌ Lỗi: Không nhận được dữ liệu game sau 30 giây.[/]")
            console.print("[yellow]Vui lòng kiểm tra lại kết nối mạng và link đăng nhập. Quay lại menu chính.[/yellow]", style="yellow")
            time.sleep(3)
            return

    poller = BalancePoller(USER_ID, SECRET_KEY, poll_seconds=max(1, int(BALANCE_POLL_INTERVAL)), on_balance=None, on_error=None, on_status=None)
    poller.start()

    console.print("\n[bold green]✅ Kết nối thành công! Bắt đầu hiển thị giao diện.[/bold green]")
    time.sleep(2)

    def generate_layout() -> Table:
        """Tạo layout chính theo cấu trúc dashboard, gọn gàng và chuyên nghiệp."""
        border_color = _rainbow_border_style()
        is_mobile = console.width < 100

        if is_mobile:
            # Trên điện thoại, xếp chồng các thành phần theo chiều dọc
            main_layout = Table.grid(expand=True, pad_edge=False)
            main_layout.add_row(build_rooms_grid(border_color=border_color))
            main_layout.add_row(build_mid(border_color=border_color))
            main_layout.add_row(build_bet_table(border_color=border_color))
        else:
            # Trên máy tính, sử dụng lưới 2 cột để tối ưu không gian
            main_grid = Table.grid(expand=True, pad_edge=False)
            main_grid.add_column("main", ratio=60)
            main_grid.add_column("side", ratio=40)
            # Sử dụng grid cho cột bên phải để đảm bảo các thành phần con co giãn theo chiều dọc
            right_column_grid = Table.grid(expand=True, pad_edge=False)
            right_column_grid.add_row(build_mid(border_color=border_color))
            right_column_grid.add_row(build_bet_table(border_color=border_color))
            main_grid.add_row(build_rooms_grid(border_color=border_color), right_column_grid)
            main_layout = main_grid

        root_layout = Table.grid(expand=True, pad_edge=False)
        root_layout.add_row(build_header(border_color=border_color))
        root_layout.add_row(build_marquee())
        root_layout.add_row(main_layout)
        return root_layout

    with Live(generate_layout(), refresh_per_second=4, console=console, screen=True) as live:
        try:
            while not stop_flag:
                live.update(generate_layout())
                time.sleep(0.25)
            console.print("[bold yellow]Tool đã dừng theo yêu cầu hoặc đạt mục tiêu.[/]")
        except KeyboardInterrupt:
            console.print("[yellow]Thoát bằng người dùng.[/]")
            poller.stop()

def main():
    console.clear()
    slow_print("⚡CHÀO MỪNG ĐẾN VỚI VUA THOÁT HIỂM TNTOOL⚡", delay=0.02, style="bold magenta")
    time.sleep(0.5)
    boot_checks = [
        "KIỂM TRA CẬP NHẬT", "THƯ VIỆN HỖ TRỢ...", "KIỂM TRA MẠNG...",
        "KIỂM TRA LOẠI ĐIẸN THOẠI...", "ĐÃ SẴN SÀNG CHIẾN!!"
    ]
    for check in boot_checks:
        console.print(f"[green]  [✓] {check}[/green]")
        time.sleep(random.uniform(0.1, 0.3))
    time.sleep(1)

    while True:
        global stop_flag
        stop_flag = False
        
        console.clear()
        console.print(Panel(Text("MENU THIẾT LẬP", justify="center", style="bold magenta"), box=box.DOUBLE, border_style="magenta"))
        
        menu_table = Table(box=None, show_header=False)
        menu_table.add_column(style="bold yellow", width=3)
        menu_table.add_column()
        menu_table.add_row("1", "Chọn tài khoản và chơi (tùy chỉnh)")
        menu_table.add_row("2", "Thêm tài khoản mới")
        menu_table.add_row("3", "Xóa tài khoản")
        menu_table.add_row("4", "Cài đặt & Lưu cấu hình chạy")
        menu_table.add_row("5", "Vào chơi theo cấu hình đã cài")
        menu_table.add_row("q", "Thoát chương trình")
        console.print(menu_table)
        
        choice = Prompt.ask("\n>> Lựa chọn của bạn", choices=['1','2','3','4','5','q'], default='q').lower()

        if choice == '1':
            console.clear()
            if select_account():
                if prompt_settings():
                    start_game_flow()
        elif choice == '2':
            console.clear()
            add_new_account(load_accounts())
            time.sleep(2)
        elif choice == '3':
            console.clear()
            delete_account(load_accounts())
            time.sleep(2)
        elif choice == '4':
            console.clear()
            if prompt_settings():
                save_strategy_config()
                console.print("[bold green]✅ Cấu hình đã được lưu thành công![/bold green]")
            else:
                console.print("[yellow]Đã hủy cài đặt.[/yellow]")
            time.sleep(2)
        elif choice == '5':
            console.clear()
            if select_account():
                if load_strategy_config():
                    start_game_flow()
                else:
                    time.sleep(2)
        elif choice == 'q':
            console.print("[bold cyan]Tạm biệt![/bold cyan]")
            break

if __name__ == "__main__":
    main()
