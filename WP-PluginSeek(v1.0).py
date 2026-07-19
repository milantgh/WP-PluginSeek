# -*- coding: utf-8 -*-
import tkinter as tk
from tkinter import filedialog, scrolledtext, messagebox
import requests
import concurrent.futures
import random
import time
from threading import Lock, Thread
from urllib.parse import urlparse
import re
import os
from bs4 import BeautifulSoup
from collections import deque
import csv

# ===================== 全局常量配置 =====================
THREAD_LOCK = Lock()
LOG_QUEUE = deque(maxlen=1200)
LOG_QUEUE_LOCK = Lock()
MAX_WORKER = 5
MIN_SLEEP = 0.18
MAX_SLEEP = 0.4
CHUNK_STEP = 1200
HTTP_TIMEOUT = 3
CSV_OUTPUT = "scan_result.csv"
DICT_FILE = "plugins_slug.txt"
WP_SVN_SOURCE = "http://plugins.svn.wordpress.org/"
CSV_HEADER = ["扫描域名", "来源标识", "插件Slug", "资源链接/目录状态码"]
# 增强UA防拦截
REQ_HEADERS = {
    "User-Agent": "Mozilla/5.0 (Windows NT 6.1; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36",
    "Connection": "close",
    "Accept-Language": "zh-CN,zh;q=0.9",
    "Cache-Control": "max-age=0",
    "Referer": "https://google.com"
}

def init_csv_header():
    if not os.path.exists(CSV_OUTPUT):
        with open(CSV_OUTPUT, "w", newline="", encoding="utf-8-sig") as f:
            writer = csv.writer(f, quoting=csv.QUOTE_ALL)
            writer.writerow(CSV_HEADER)

def append_site_to_csv(domain, data_list):
    with open(CSV_OUTPUT, "a", newline="", encoding="utf-8-sig") as f:
        writer = csv.writer(f, quoting=csv.QUOTE_ALL)
        if len(data_list) == 0:
            writer.writerow([domain, "无", "none", "未发现任何插件/ver资源"])
        else:
            for item in data_list:
                if len(item) == 3:
                    slug, tag, link = item
                    writer.writerow([domain, tag, slug, link])
                else:
                    slug, code = item
                    writer.writerow([domain, "dict_dir", slug, f"状态码:{code}"])

def normalize_url(raw_url):
    raw = raw_url.strip()
    if not raw:
        return None
    if not raw.startswith(("http://", "https://")):
        raw = f"http://{raw}"
    try:
        parse_res = urlparse(raw)
        if not parse_res.netloc:
            return None
        return f"{parse_res.scheme}://{parse_res.netloc}".rstrip("/")
    except:
        return None

# 页面提取函数：完全不依赖探测目录
def extract_plugin_from_html(target_url):
    try:
        resp = requests.get(target_url, headers=REQ_HEADERS, timeout=HTTP_TIMEOUT)
        self_html_code = resp.status_code
        html_text = resp.text
        # 兼容 plugin/plugins 单复数、无ver参数链接
        reg_pattern = re.compile(r'["\'](https?://.*?/(plugins?)/([\w\-]+)/.*?)["\']')
        all_match = reg_pattern.findall(html_text)
        result = []
        seen_slug = set()
        for full_href, folder_type, slug in all_match:
            if slug not in seen_slug:
                seen_slug.add(slug)
                result.append((slug, "html_plugin", full_href))
        # 打印页面匹配详情
        app.log_print(f"[页面请求状态码：{self_html_code} 匹配原始链接{len(all_match)}条，去重插件{len(result)}个]")
        return result
    except requests.exceptions.Timeout:
        app.log_print(f"[页面提取超时 {target_url}]")
        return []
    except requests.exceptions.ConnectionError:
        app.log_print(f"[页面无法连接 {target_url}]")
        return []
    except Exception as e:
        app.log_print(f"[页面解析异常 {target_url} 错误：{str(e)}]")
        return []

class WPScanGUI:
    def __init__(self, root_window):
        self.root = root_window
        self.root.title("信安西部-明镜高悬实验室-WP插件精准扫描系统-WP-PluginSeek(v1.0)")
        self.root.geometry("1040x680")
        self.root.minsize(900, 620)
        self.root.protocol("WM_DELETE_WINDOW", self.on_app_close)
        # 全局标记
        self.is_scanning = False
        self.is_updating_dict = False
        # 变量绑定
        self.var_single_url = tk.StringVar()
        self.var_batch_path = tk.StringVar()
        self.var_dict_path = tk.StringVar()
        self.var_scan_dir = tk.StringVar(value="/wp-content/plugins") # 仅模式2使用
        # 互斥单选：0=页面提取(不用探测目录) 1=字典爆破(需要探测目录)
        self.scan_mode = tk.IntVar(value=0)
        # 缓存
        self.scan_cache = {}
        self.batch_domain_list = []
        self.slug_dict_list = []

        # 网格自适应权重
        self.root.rowconfigure(0, weight=0)
        self.root.rowconfigure(1, weight=0)
        self.root.rowconfigure(2, weight=0)
        self.root.rowconfigure(3, weight=0)
        self.root.rowconfigure(4, weight=10)
        self.root.columnconfigure(0, weight=1)

        # 1. 单个域名输入行
        frame_single = tk.Frame(root_window, bd=1, relief=tk.GROOVE)
        frame_single.grid(row=0, column=0, sticky="nsew", padx=10, pady=2)
        frame_single.columnconfigure(1, weight=1)
        tk.Label(frame_single, text="单个扫描域名：", width=14).grid(row=0, column=0, padx=6, pady=6)
        tk.Entry(frame_single, textvariable=self.var_single_url).grid(row=0, column=1, sticky="ew", padx=6, pady=6)

        # 2. 批量URL文件行
        frame_batch = tk.Frame(root_window, bd=1, relief=tk.GROOVE)
        frame_batch.grid(row=1, column=0, sticky="nsew", padx=10, pady=2)
        frame_batch.columnconfigure(1, weight=1)
        tk.Label(frame_batch, text="批量URL文本文件：", width=14).grid(row=0, column=0, padx=6, pady=6)
        tk.Entry(frame_batch, textvariable=self.var_batch_path).grid(row=0, column=1, sticky="ew", padx=6, pady=6)
        tk.Button(frame_batch, text="加载列表", command=self.load_batch_file).grid(row=0, column=2, padx=6, pady=6)

        # 3. 字典&探测目录区域（仅模式2生效）
        frame_dict = tk.Frame(root_window, bd=1, relief=tk.GROOVE)
        frame_dict.grid(row=2, column=0, sticky="nsew", padx=10, pady=2)
        frame_dict.columnconfigure(1, weight=1)
        # 字典路径行
        tk.Label(frame_dict, text="插件Slug字典：", width=14).grid(row=0, column=0, padx=6, pady=6)
        self.entry_dict_path = tk.Entry(frame_dict, textvariable=self.var_dict_path)
        self.entry_dict_path.grid(row=0, column=1, sticky="ew", padx=6, pady=6)
        tk.Button(frame_dict, text="本地字典", command=self.load_local_dict).grid(row=0, column=2, padx=3, pady=6)
        self.update_dict_btn = tk.Button(frame_dict, text="一键在线更新WP官方字典", bg="#ff8800", fg="white", command=self.start_update_dict_thread)
        self.update_dict_btn.grid(row=0, column=3, padx=6, pady=6)
        # 探测目录行（仅模式2可用）
        tk.Label(frame_dict, text="字典探测目录：", width=14).grid(row=1, column=0, padx=6, pady=6)
        self.label_scan_dir = tk.Label(frame_dict, text="字典探测目录：", width=14)
        self.entry_scan_dir = tk.Entry(frame_dict, textvariable=self.var_scan_dir)
        self.label_scan_dir.grid(row=1, column=0, padx=6, pady=6)
        self.entry_scan_dir.grid(row=1, column=1, sticky="ew", padx=6, pady=6)
        # 初始化控件状态：默认模式1，探测目录置灰
        self.set_dir_widget_state()

        # 4. 模式选择+功能按钮（无重复探测目录输入框）
        frame_mode_btn = tk.Frame(root_window, bd=1, relief=tk.GROOVE)
        frame_mode_btn.grid(row=3, column=0, sticky="nsew", padx=10, pady=2)
        # 互斥单选，切换自动重置数据+切换控件灰化状态
        tk.Radiobutton(frame_mode_btn, text="模式1：页面源码提取（无需字典/探测目录）", variable=self.scan_mode, value=0, command=self.on_mode_change).pack(side="left", padx=6, pady=4)
        tk.Radiobutton(frame_mode_btn, text="模式2：字典目录爆破（需字典+探测目录）", variable=self.scan_mode, value=1, command=self.on_mode_change).pack(side="left", padx=6, pady=4)
        # 缩小功能按钮
        self.btn_start = tk.Button(frame_mode_btn, text="开始扫描", bg="#2ea043", fg="white", width=10, height=1, command=self.start_scan_thread)
        self.btn_start.pack(side="left", padx=6, pady=4)
        self.btn_export = tk.Button(frame_mode_btn, text="导出CSV", bg="#2383e2", fg="white", width=10, height=1, command=self.export_cache_csv)
        self.btn_export.pack(side="left", padx=6, pady=4)
        self.btn_clear_log = tk.Button(frame_mode_btn, text="清空日志", width=8, height=1, command=self.clear_all_log)
        self.btn_clear_log.pack(side="left", padx=6, pady=4)

        # 5. 日志输出区，消除底部空白
        frame_log = tk.Frame(root_window)
        frame_log.grid(row=4, column=0, sticky="nsew", padx=10, pady=(6, 0))
        frame_log.rowconfigure(1, weight=1)
        frame_log.columnconfigure(0, weight=1)
        tk.Label(frame_log, text="实时扫描日志缓冲区").grid(row=0, column=0, sticky="w")
        self.log_textbox = scrolledtext.ScrolledText(frame_log, wrap="word")
        self.log_textbox.grid(row=1, column=0, sticky="nsew", pady=0)

        init_csv_header()
        self.root.after(10, self.center_window)
        self.refresh_log_timer()

    # 切换模式回调：1.清空缓存日志 2.切换探测目录控件启用/置灰
    def on_mode_change(self):
        self.scan_cache.clear()
        self.batch_domain_list.clear()
        self.log_textbox.delete(1.0, tk.END)
        self.set_dir_widget_state()
        mode = self.scan_mode.get()
        if mode == 0:
            self.log_print("[提示] 当前模式1：页面源码提取，不使用字典与探测目录参数")
        else:
            self.log_print("[提示] 当前模式2：字典目录爆破，将读取字典与探测目录参数")

    # 控制探测目录、字典输入框灰化：模式1不可编辑，模式2可编辑
    def set_dir_widget_state(self):
        mode = self.scan_mode.get()
        if mode == 0:
            # 模式1：置灰，不可修改
            self.entry_scan_dir.config(state=tk.DISABLED, bg="#dddddd")
            self.entry_dict_path.config(state=tk.DISABLED, bg="#dddddd")
            self.update_dict_btn.config(state=tk.DISABLED, bg="#aaaaaa")
        else:
            # 模式2：正常可编辑
            self.entry_scan_dir.config(state=tk.NORMAL, bg="#ffffff")
            self.entry_dict_path.config(state=tk.NORMAL, bg="#ffffff")
            self.update_dict_btn.config(state=tk.NORMAL, bg="#ff8800")

    def on_app_close(self):
        self.root.destroy()
        os._exit(0)

    def log_print(self, msg):
        with LOG_QUEUE_LOCK:
            LOG_QUEUE.append(msg)

    def refresh_log_timer(self):
        global LOG_QUEUE
        with LOG_QUEUE_LOCK:
            if len(LOG_QUEUE) > 0:
                batch_text = "\n".join(LOG_QUEUE) + "\n"
                self.log_textbox.insert(tk.END, batch_text)
                self.log_textbox.see(tk.END)
                LOG_QUEUE.clear()
        self.root.after(180, self.refresh_log_timer)

    def clear_all_log(self):
        self.log_textbox.delete(1.0, tk.END)

    def center_window(self):
        win_w = 1040
        win_h = 680
        screen_w = self.root.winfo_screenwidth()
        screen_h = self.root.winfo_screenheight()
        x = int((screen_w - win_w) / 2)
        y = int((screen_h - win_h) / 2)
        self.root.geometry(f"{win_w}x{win_h}+{x}+{y}")

    # 字典在线更新
    def start_update_dict_thread(self):
        if self.is_updating_dict:
            messagebox.showinfo("提示", "字典更新任务正在运行，请勿重复点击！")
            return
        # 模式2才允许更新字典
        if self.scan_mode.get() != 1:
            messagebox.showinfo("提示", "当前为页面提取模式，无需操作字典！切换模式2后再更新")
            return
        self.is_updating_dict = True
        self.update_dict_btn.config(state=tk.DISABLED)
        t = Thread(target=self.update_dict_task, daemon=True)
        t.start()

    def update_dict_task(self):
        self.log_print("[字典更新] 正在拉取WordPress官方SVN插件列表...")
        headers = {"User-Agent": "Mozilla/5.0 (Windows NT 6.1; Win64; x64) Chrome/120.0.0.0 Safari/537.36"}
        slugs = []
        try:
            resp = requests.get(WP_SVN_SOURCE, headers=headers, timeout=10)
            soup = BeautifulSoup(resp.text, "html.parser")
            for a in soup.find_all("a"):
                name = a.get("href").strip("/")
                if name and name != "..":
                    slugs.append(name)
            if len(slugs) == 0:
                self.log_print("[严重警告] SVN抓取0条，放弃覆盖本地字典！")
                self.is_updating_dict = False
                self.update_dict_btn.config(state=tk.NORMAL)
                return
            with open(DICT_FILE, "w", encoding="utf-8") as f:
                for s in slugs:
                    f.write(f"{s}\n")
            self.slug_dict_list = list(set(slugs))
            self.var_dict_path.set(os.path.abspath(DICT_FILE))
            self.log_print(f"[字典更新完成] 共 {len(slugs)} 条插件，已覆盖保存")
        except requests.exceptions.Timeout:
            self.log_print("[错误] SVN服务器超时，请切换代理/热点")
        except Exception as e:
            self.log_print(f"[字典更新失败] {str(e)}")
        self.is_updating_dict = False
        self.update_dict_btn.config(state=tk.NORMAL)

    # 本地加载字典
    def load_local_dict(self):
        if self.scan_mode.get() != 1:
            messagebox.showinfo("提示", "当前页面提取模式无需加载字典！切换模式2使用")
            return
        fp = filedialog.askopenfilename(filetypes=[("文本文件", "*.txt")])
        if not fp:
            return
        self.var_dict_path.set(fp)
        try:
            with open(fp, "r", encoding="utf-8") as f:
                lines = [i.strip() for i in f if i.strip()]
            self.slug_dict_list = list(set(lines))
            self.log_print(f"[本地字典加载成功，共 {len(self.slug_dict_list)} 条]")
        except Exception as err:
            messagebox.showerror("读取失败", str(err))

    # 加载批量URL
    def load_batch_file(self):
        fp = filedialog.askopenfilename(filetypes=[("文本文件", "*.txt")])
        if not fp:
            return
        self.var_batch_path.set(fp)
        temp_list = []
        try:
            with open(fp, "r", encoding="utf-8") as f:
                for raw_line in f:
                    clean_domain = normalize_url(raw_line)
                    if clean_domain and clean_domain not in temp_list:
                        temp_list.append(clean_domain)
            self.batch_domain_list = temp_list
            self.log_print(f"[批量URL加载完成，有效站点 {len(temp_list)} 个]")
        except Exception as err:
            messagebox.showerror("读取失败", str(err))

    # 仅模式2调用：字典目录请求（仅模式2读取探测目录）
    def request_plugin_dir(self, base_domain, slug, result_container):
        custom_dir = self.var_scan_dir.get().strip()
        target = f"{base_domain}{custom_dir}{slug}/"
        try:
            time.sleep(random.uniform(MIN_SLEEP, MAX_SLEEP))
            resp = requests.get(target, headers=REQ_HEADERS, timeout=HTTP_TIMEOUT, allow_redirects=False)
            if resp.status_code in (200, 403):
                result_container.append((slug, str(resp.status_code)))
                self.log_print(f"[字典识别] {base_domain} {slug} 目录{custom_dir} 状态码:{resp.status_code}")
        except Exception:
            pass

    # 单个站点扫描：严格隔离两套模式逻辑
    def scan_single_target(self, domain):
        self.log_print(f"\n===== 开始扫描 {domain} =====")
        site_data = []
        mode = self.scan_mode.get()
        # ========== 模式1：页面提取，完全不碰探测目录、字典 ==========
        if mode == 0:
            self.log_print(f"[{domain}] 模式1运行：页面源码提取")
            html_items = extract_plugin_from_html(domain)
            for slug, tag, link in html_items:
                site_data.append((slug, tag, link))
                self.log_print(f"[页面识别插件] {domain} {slug} 链接:{link}")
        # ========== 模式2：字典爆破，读取探测目录与字典 ==========
        elif mode == 1:
            if len(self.slug_dict_list) == 0:
                self.log_print(f"[{domain}] 未加载插件字典，跳过目录探测")
            else:
                total = len(self.slug_dict_list)
                scan_dir = self.var_scan_dir.get().strip()
                for offset in range(0, total, CHUNK_STEP):
                    chunk = self.slug_dict_list[offset:offset+CHUNK_STEP]
                    self.log_print(f"[{domain}] 字典分片 {offset+1} ~ {min(offset+CHUNK_STEP, total)} 探测目录:{scan_dir}")
                    with concurrent.futures.ThreadPoolExecutor(max_workers=MAX_WORKER) as pool:
                        task = [pool.submit(self.request_plugin_dir, domain, s, site_data) for s in chunk]
                        concurrent.futures.wait(task, timeout=12)
        # 结果去重
        seen = set()
        final_data = []
        for item in site_data:
            key = str(item[0])
            if key not in seen:
                seen.add(key)
                final_data.append(item)
        append_site_to_csv(domain, final_data)
        self.scan_cache[domain] = final_data
        self.log_print(f"===== {domain} 扫描结束，共识别 {len(final_data)} 条插件/资源 =====\n")

    # 批量扫描总调度
    def scan_all_batch_task(self):
        self.scan_cache.clear()
        target_all = []
        single_raw = self.var_single_url.get().strip()
        if single_raw:
            clean_single = normalize_url(single_raw)
            if clean_single:
                target_all.append(clean_single)
        target_all.extend(self.batch_domain_list)
        target_all = list(set(target_all))
        # 前置校验
        if len(target_all) == 0:
            self.log_print("[错误] 未填写任何待扫描站点！")
            self.is_scanning = False
            self.btn_start.config(state=tk.NORMAL)
            return
        mode = self.scan_mode.get()
        # 模式2单独校验字典
        if mode == 1 and len(self.slug_dict_list) == 0:
            messagebox.showwarning("提示", "当前字典爆破模式，请先加载/更新插件字典！")
            self.is_scanning = False
            self.btn_start.config(state=tk.NORMAL)
            return
        # 打印当前运行模式
        if mode == 0:
            self.log_print(f"批量扫描启动，共{len(target_all)}个站点，模式1页面提取，不使用探测目录，CSV:{os.path.abspath(CSV_OUTPUT)}")
        else:
            self.log_print(f"批量扫描启动，共{len(target_all)}个站点，模式2字典爆破，探测目录:{self.var_scan_dir.get()}，CSV:{os.path.abspath(CSV_OUTPUT)}")
        for dom in target_all:
            self.scan_single_target(dom)
        self.log_print("\n√ 全部站点扫描完成，数据已持久化保存CSV！")
        self.is_scanning = False
        self.btn_start.config(state=tk.NORMAL)

    def start_scan_thread(self):
        if self.is_scanning:
            messagebox.showinfo("提示", "扫描任务正在运行，禁止重复启动！")
            return
        self.is_scanning = True
        self.btn_start.config(state=tk.DISABLED)
        t = Thread(target=self.scan_all_batch_task, daemon=True)
        t.start()

    # 导出缓存CSV
    def export_cache_csv(self):
        if len(self.scan_cache) == 0:
            messagebox.showinfo("提示", "暂无扫描缓存，无法导出！")
            return
        save_path = filedialog.asksaveasfilename(
            defaultextension=".csv",
            filetypes=[("CSV表格文件 Excel直接打开", "*.csv")],
            initialfile="wp_scan_export.csv"
        )
        if not save_path:
            return
        with open(save_path, "w", newline="", encoding="utf-8-sig") as f:
            writer = csv.writer(f, quoting=csv.QUOTE_ALL)
            writer.writerow(CSV_HEADER)
            for dom, data_list in self.scan_cache.items():
                if len(data_list) == 0:
                    writer.writerow([dom, "无", "none", "未发现任何插件/ver资源"])
                else:
                    for item in data_list:
                        if len(item) == 3:
                            slug, tag, link = item
                            writer.writerow([dom, tag, slug, link])
                        else:
                            slug, code = item
                            writer.writerow([dom, "dict_dir", slug, f"状态码:{code}"])
        messagebox.showinfo("导出成功", f"缓存扫描数据导出至：{save_path}")

# 全局实例供页面函数调用日志
app = None
if __name__ == "__main__":
    main_win = tk.Tk()
    app = WPScanGUI(main_win)
    main_win.mainloop()