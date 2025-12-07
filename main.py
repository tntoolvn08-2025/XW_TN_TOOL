import argparse
import sys

def main():
    parser = argparse.ArgumentParser(description="Tool chính")
    parser.add_argument("--password", type=str, required=True, help="Mật mã để chạy tool.")
    args = parser.parse_args()

    # Thay đổi mật mã ở đây
    correct_password = "con_cac"

    if args.password == correct_password:
        print("Mật mã chính xác. Đang chạy tool...")
        # =================================================
        # Thêm code chính của bạn vào đây
        # Ví dụ:
        print("Tool đang hoạt động!")
        # =================================================
    else:
        print("Mật mã không chính xác. Vui lòng thử lại.")
        sys.exit(1)

if __name__ == "__main__":
    main()
