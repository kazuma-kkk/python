"""
优雅五子棋 — 最终美化版
==================================================
技术栈：Python + pygame
功能特性：
    1. 900x650 窗口，左侧棋盘 + 右侧控制面板
    2. 15x15 标准棋盘，日式榧木色调多层木框
    3. 鼠标点击落子，黑白棋子带径向渐变 3D 效果
    4. 双人对战 / 人机对战（AI 优先防守再进攻）
    5. 胜负判定 + 脉冲动画胜利横幅
    6. 悔棋 / 重新开始 / 切换模式 / 退出
    7. 落子音效 + 获胜连线呼吸光晕
运行方式：python gobang.py
依赖：pip install pygame
"""

import sys
import os
import math
import random
import pygame
from pygame.locals import QUIT, MOUSEBUTTONDOWN, KEYDOWN, K_r, K_z, K_ESCAPE, K_p

# ==================== 全局配置 ====================
WINDOW_WIDTH = 900
WINDOW_HEIGHT = 650

# ---------- 布局常量 ----------
BOARD_AREA_WIDTH = 560
BOARD_LEFT = 0
BOARD_TOP = 20
BOARD_MARGIN = 35

BOARD_SIZE = 15
BOARD_PIXEL = BOARD_AREA_WIDTH - 2 * BOARD_MARGIN  # 490
assert BOARD_PIXEL % (BOARD_SIZE - 1) == 0
GRID_SIZE = BOARD_PIXEL // (BOARD_SIZE - 1)         # 35
PIECE_RADIUS = GRID_SIZE // 2 - 2                   # 15

PANEL_LEFT = BOARD_AREA_WIDTH + 4
PANEL_WIDTH = WINDOW_WIDTH - PANEL_LEFT
PANEL_PAD = 22

# ---------- 颜色配置（日式暖色调） ----------
BG_COLOR = (250, 243, 230)           # 暖白 / 奶油色底
PANEL_BG = (240, 232, 218)           # 面板：浅亚麻色

# 棋盘边框 — 榧木层次感
FRAME_OUTER = (85, 50, 28)           # 外框：深胡桃木
FRAME_MID = (130, 80, 45)            # 中框
FRAME_INNER = (170, 125, 80)         # 内框
BOARD_COLOR = (218, 185, 140)        # 棋盘面：榧木色
LINE_COLOR = (60, 40, 22)            # 网格线：柔和深棕

# UI 文字
TEXT_COLOR = (52, 35, 16)            # 主文字：浓茶色
TEXT_LIGHT = (125, 95, 60)           # 次要文字
ACCENT_COLOR = (185, 50, 45)         # 强调色：朱红
HIGHLIGHT_COLOR = (240, 65, 50)      # 高亮

# 棋子
BLACK_PIECE_BASE = (38, 33, 30)      # 黑子：炭黑
WHITE_PIECE_BASE = (248, 245, 238)   # 白子：珍珠白

# 按钮
BUTTON_BG = (205, 178, 140)
BUTTON_HOVER = (228, 202, 165)
BUTTON_BORDER = (142, 112, 68)
BUTTON_SHADOW = (175, 148, 115)

# 棋子常量
EMPTY = 0
BLACK = 1
WHITE = 2

# ==================== 游戏类 ====================
class GobangGame:
    """五子棋游戏主类 — 最终美化版"""

    def __init__(self):
        pygame.init()
        try:
            pygame.mixer.init()
            self.sound_enabled = True
            pygame.mixer.set_num_channels(8)
        except pygame.error:
            self.sound_enabled = False

        self.screen = pygame.display.set_mode((WINDOW_WIDTH, WINDOW_HEIGHT))
        pygame.display.set_caption("优雅五子棋")
        try:
            icon = pygame.Surface((32, 32))
            icon.fill(BG_COLOR)
            pygame.draw.circle(icon, BLACK_PIECE_BASE, (16, 16), 14)
            pygame.display.set_icon(icon)
        except Exception:
            pass

        # 字体
        self.font_title = self._safe_font(28)
        self.font_info = self._safe_font(18)
        self.font_hint = self._safe_font(14)
        self.font_banner = self._safe_font(46)      # 胜利横幅大字
        self.font_label = self._safe_font(11)
        self.font_menu_title = self._safe_font(38)   # 菜单标题
        self.font_menu_opt = self._safe_font(20)     # 菜单选项标签
        self.font_menu_val = self._safe_font(18)     # 菜单选项值
        self.font_menu_btn = self._safe_font(16)     # 菜单按钮文字

        # 棋盘原点
        self.board_origin_x = BOARD_LEFT + BOARD_MARGIN
        self.board_origin_y = BOARD_TOP + BOARD_MARGIN

        self.panel_rect = pygame.Rect(PANEL_LEFT, 0, PANEL_WIDTH, WINDOW_HEIGHT)
        self.panel_buttons = []
        self.menu_buttons = []
        self._init_panel_buttons()
        self._init_menu_buttons()

        # 菜单配置状态
        self.game_state = "menu"       # "menu" | "playing"
        self.game_type = "gobang"      # "gobang" | "go"
        self.game_mode = "pvp"
        self.ai_difficulty = "medium"  # "easy" | "medium" | "hard"
        self.player_color = "random"   # "random" | "black" | "white"
        self.actual_player_color = BLACK  # 实际对局中的玩家颜色

        # 游戏状态
        self.board = [[EMPTY for _ in range(BOARD_SIZE)] for _ in range(BOARD_SIZE)]
        self.move_history = []
        self.current_player = BLACK
        self.winner = EMPTY
        self.win_line = []
        self.flash_timer = 0
        self.ai_thinking = False
        self.ai_move_at = 0

        # 围棋专用状态
        self.go_black_captures = 0     # 黑方提子数（得分）
        self.go_white_captures = 0     # 白方提子数（得分）
        self.go_ko_point = None        # 劫争禁入点 (col, row)
        self.go_prev_board_hash = ""   # 上一步棋盘哈希（劫争检测）
        self.go_prev_capture_count = 0 # 上一步提子数量
        self.go_pass_count = 0         # 连续 pass 计数（两次 pass 结束对局）
        self.go_last_pass = None       # 上一次 pass 的玩家
        self.go_board_history = []     # 历史棋盘哈希（位置超级劫）
        self.go_game_ended = False     # 对局是否已进入数子阶段
        self._go_score_detail = {}     # 数目计分详情

        # Toast 提示（棋盘中央短暂提示文字）
        self.toast_message = ""
        self.toast_expire = 0

        # 预生成音效 & 棋子表面
        self.place_sound = self._make_click_sound() if self.sound_enabled else None
        self._cache_piece_surfaces()

    # ---------- 工具方法 ----------
    def _init_panel_buttons(self):
        """面板按钮：药丸风格、更高更舒适"""
        bx = PANEL_LEFT + PANEL_PAD
        bw = PANEL_WIDTH - PANEL_PAD * 2
        bh = 40
        gap = 8
        base_y = WINDOW_HEIGHT - 5 * (bh + gap) - 14
        self.panel_buttons = [
            {"rect": pygame.Rect(bx, base_y, bw, bh), "text": "Pass (P)", "action": "pass_go", "go_only": True},
            {"rect": pygame.Rect(bx, base_y + (bh + gap), bw, bh), "text": "重新开始 (R)", "action": "reset"},
            {"rect": pygame.Rect(bx, base_y + (bh + gap) * 2, bw, bh), "text": "悔棋 (Z)", "action": "undo"},
            {"rect": pygame.Rect(bx, base_y + (bh + gap) * 3, bw, bh), "text": "返回菜单", "action": "to_menu"},
            {"rect": pygame.Rect(bx, base_y + (bh + gap) * 4, bw, bh), "text": "退出 (ESC)", "action": "quit"},
        ]

    def _init_menu_buttons(self):
        """预游戏菜单按钮：游戏 / 模式 / 难度 / 先后手 / 开始"""
        cx = WINDOW_WIDTH // 2
        self.menu_buttons = []
        # ---- 游戏类型（五子棋 / 围棋）----
        bw, bh = 160, 44
        self.menu_buttons += [
            {"rect": pygame.Rect(cx - bw - 12, 162, bw, bh),
             "text": "五子棋", "group": "gametype", "value": "gobang"},
            {"rect": pygame.Rect(cx + 12, 162, bw, bh),
             "text": "围  棋", "group": "gametype", "value": "go"},
        ]
        # ---- 模式按钮（PVP / PVE）----
        self.menu_buttons += [
            {"rect": pygame.Rect(cx - bw - 12, 228, bw, bh),
             "text": "双人对战", "group": "mode", "value": "pvp"},
            {"rect": pygame.Rect(cx + 12, 228, bw, bh),
             "text": "人机对战", "group": "mode", "value": "pve"},
        ]
        # ---- 难度按钮（easy / medium / hard）— 仅 PVE 显示 ----
        bw2, bh2 = 100, 38
        dx = cx - bw2 * 3 // 2 - 24
        self.menu_buttons += [
            {"rect": pygame.Rect(dx, 328, bw2, bh2),
             "text": "简单", "group": "difficulty", "value": "easy"},
            {"rect": pygame.Rect(dx + bw2 + 12, 328, bw2, bh2),
             "text": "中等", "group": "difficulty", "value": "medium"},
            {"rect": pygame.Rect(dx + (bw2 + 12) * 2, 328, bw2, bh2),
             "text": "困难", "group": "difficulty", "value": "hard"},
        ]
        # ---- 先后手按钮（black / white / random）— 仅 PVE 显示 ----
        dx2 = cx - bw2 * 3 // 2 - 24
        self.menu_buttons += [
            {"rect": pygame.Rect(dx2, 418, bw2, bh2),
             "text": "执黑", "group": "color", "value": "black"},
            {"rect": pygame.Rect(dx2 + bw2 + 12, 418, bw2, bh2),
             "text": "执白", "group": "color", "value": "white"},
            {"rect": pygame.Rect(dx2 + (bw2 + 12) * 2, 418, bw2, bh2),
             "text": "随机", "group": "color", "value": "random"},
        ]
        # ---- 开始按钮 ----
        self.menu_buttons.append(
            {"rect": pygame.Rect(cx - 90, 510, 180, 52),
             "text": "开始游戏", "group": "start", "value": "start"}
        )

    @staticmethod
    def _safe_font(size):
        candidates = [
            os.path.join(os.environ.get("WINDIR", r"C:\Windows"), "Fonts", "msyh.ttc"),
            os.path.join(os.environ.get("WINDIR", r"C:\Windows"), "Fonts", "msyhbd.ttc"),
            os.path.join(os.environ.get("WINDIR", r"C:\Windows"), "Fonts", "simhei.ttf"),
            os.path.join(os.environ.get("WINDIR", r"C:\Windows"), "Fonts", "simsun.ttc"),
        ]
        for path in candidates:
            if os.path.isfile(path):
                try:
                    return pygame.font.Font(path, size)
                except Exception:
                    continue
        try:
            return pygame.font.SysFont("microsoftyahei", size)
        except Exception:
            pass
        return pygame.font.Font(None, size)

    @staticmethod
    def _make_click_sound():
        try:
            import numpy as np
            sample_rate = 22050
            duration = 0.06
            t = np.linspace(0, duration, int(sample_rate * duration), False)
            envelope = np.exp(-t * 50)
            wave = (np.sin(2 * np.pi * 900 * t) * envelope * 4096).astype(np.int16)
            stereo = np.column_stack((wave, wave))
            return pygame.sndarray.make_sound(stereo)
        except Exception:
            return None

    def play_sound(self, sound):
        if self.sound_enabled and sound is not None:
            try:
                sound.play()
            except Exception:
                pass

    # ---------- 棋子 3D 表面缓存 ----------
    def _cache_piece_surfaces(self):
        """预渲染带径向渐变 + 高光的棋子表面"""
        d = PIECE_RADIUS * 2
        self._piece_black = pygame.Surface((d, d), pygame.SRCALPHA)
        self._piece_white = pygame.Surface((d, d), pygame.SRCALPHA)

        cx = cy = PIECE_RADIUS
        r = PIECE_RADIUS
        # 核心区域（85% 半径内）保持完全不透明，仅在边缘 15% 平滑抗锯齿
        core_ratio = 0.85

        # 黑子：径向渐变从炭黑到边缘深黑
        for dx in range(d):
            for dy in range(d):
                dist = math.hypot(dx - cx, dy - cy)
                if dist > r:
                    continue
                t_val = dist / r  # 0=中心, 1=边缘
                # 颜色渐变：中心稍亮，边缘更深
                t_color = t_val ** 1.5
                rr = int(45 + (1 - t_color) * 55)
                gg = int(38 + (1 - t_color) * 45)
                bb = int(34 + (1 - t_color) * 40)
                # 透明度：核心全不透明，边缘快速衰减
                if t_val <= core_ratio:
                    a = 255
                else:
                    t_edge = (t_val - core_ratio) / (1 - core_ratio)
                    a = int((1 - t_edge ** 2) * 255)
                self._piece_black.set_at((dx, dy), (rr, gg, bb, a))
        # 高光：左上角小白斑
        hl_r = r // 2
        hl_cx = cx - r // 3
        hl_cy = cy - r // 3
        for dx in range(max(0, hl_cx - hl_r), min(d, hl_cx + hl_r)):
            for dy in range(max(0, hl_cy - hl_r), min(d, hl_cy + hl_r)):
                dist = math.hypot(dx - hl_cx, dy - hl_cy)
                if dist < hl_r:
                    a = int(max(0, (1 - dist / hl_r) * 110))
                    existing = self._piece_black.get_at((dx, dy))
                    nr = min(255, existing[0] + 180 * a // 255)
                    ng = min(255, existing[1] + 170 * a // 255)
                    nb = min(255, existing[2] + 160 * a // 255)
                    self._piece_black.set_at((dx, dy), (nr, ng, nb, existing[3]))

        # 白子：径向渐变从珍珠白到边缘灰白
        for dx in range(d):
            for dy in range(d):
                dist = math.hypot(dx - cx, dy - cy)
                if dist > r:
                    continue
                t_val = dist / r
                # 颜色渐变
                t_color = t_val ** 1.5
                rr = int(252 - t_color * 60)
                gg = int(248 - t_color * 63)
                bb = int(241 - t_color * 60)
                # 透明度：核心全不透明，边缘快速衰减
                if t_val <= core_ratio:
                    a = 255
                else:
                    t_edge = (t_val - core_ratio) / (1 - core_ratio)
                    a = int((1 - t_edge ** 2) * 255)
                self._piece_white.set_at((dx, dy), (rr, gg, bb, a))
        # 高光
        for dx in range(max(0, hl_cx - hl_r), min(d, hl_cx + hl_r)):
            for dy in range(max(0, hl_cy - hl_r), min(d, hl_cy + hl_r)):
                dist = math.hypot(dx - hl_cx, dy - hl_cy)
                if dist < hl_r:
                    a = int(max(0, (1 - dist / hl_r) * 120))
                    existing = self._piece_white.get_at((dx, dy))
                    nr = min(255, existing[0] + 7 * a // 255)
                    ng = min(255, existing[1] + 10 * a // 255)
                    nb = min(255, existing[2] + 17 * a // 255)
                    self._piece_white.set_at((dx, dy), (nr, ng, nb, existing[3]))

        # 预缓存棋子阴影
        sd = PIECE_RADIUS * 2 + 6
        self._piece_shadow = pygame.Surface((sd, sd), pygame.SRCALPHA)
        shadow_r = PIECE_RADIUS + 1
        pygame.draw.circle(self._piece_shadow, (0, 0, 0, 80),
                           (PIECE_RADIUS + 3, PIECE_RADIUS + 4), shadow_r)
        pygame.draw.circle(self._piece_shadow, (0, 0, 0, 40),
                           (PIECE_RADIUS + 4, PIECE_RADIUS + 5), shadow_r - 1)

        # 预缓存光晕模板（满强度，每帧 set_alpha 控制呼吸）
        glow_size = PIECE_RADIUS + 6
        gs = glow_size * 2
        self._glow_template = pygame.Surface((gs, gs), pygame.SRCALPHA)
        for r in range(glow_size, 0, -1):
            a = int(255 * (r / glow_size) * 0.45)
            pygame.draw.circle(self._glow_template, HIGHLIGHT_COLOR + (a,), (glow_size, glow_size), r)

        # 预缓存 HUD 小棋子图标
        self._icon_black = self._render_icon_piece(BLACK_PIECE_BASE, 28)
        self._icon_white = self._render_icon_piece(WHITE_PIECE_BASE, 28)

    # ---------- 坐标转换 ----------
    def pixel_to_grid(self, px, py):
        return round((px - self.board_origin_x) / GRID_SIZE), round((py - self.board_origin_y) / GRID_SIZE)

    def grid_to_pixel(self, col, row):
        return self.board_origin_x + col * GRID_SIZE, self.board_origin_y + row * GRID_SIZE

    def is_valid_pos(self, col, row):
        return 0 <= col < BOARD_SIZE and 0 <= row < BOARD_SIZE and self.board[row][col] == EMPTY

    # ---------- 胜负判定 ----------
    def _scan_direction(self, col, row, dx, dy, player):
        """沿 (dx,dy) 正反方向扫描，返回 (连子数, 开端数)"""
        count = 1
        open_ends = 0
        for step in range(1, 5):
            nx, ny = col + dx * step, row + dy * step
            if 0 <= nx < BOARD_SIZE and 0 <= ny < BOARD_SIZE and self.board[ny][nx] == player:
                count += 1
            else:
                if 0 <= nx < BOARD_SIZE and 0 <= ny < BOARD_SIZE and self.board[ny][nx] == EMPTY:
                    open_ends += 1
                break
        for step in range(1, 5):
            nx, ny = col - dx * step, row - dy * step
            if 0 <= nx < BOARD_SIZE and 0 <= ny < BOARD_SIZE and self.board[ny][nx] == player:
                count += 1
            else:
                if 0 <= nx < BOARD_SIZE and 0 <= ny < BOARD_SIZE and self.board[ny][nx] == EMPTY:
                    open_ends += 1
                break
        return count, open_ends

    def check_winner(self, col, row, player):
        directions = [(1, 0), (0, 1), (1, 1), (1, -1)]
        for dx, dy in directions:
            count, _ = self._scan_direction(col, row, dx, dy, player)
            if count < 5:
                continue
            # 找到连线起点
            start_c, start_r = col, row
            for step in range(1, 5):
                nx, ny = col - dx * step, row - dy * step
                if 0 <= nx < BOARD_SIZE and 0 <= ny < BOARD_SIZE and self.board[ny][nx] == player:
                    start_c, start_r = nx, ny
                else:
                    break
            line = [(start_c + dx * step, start_r + dy * step) for step in range(5)]
            return line
        return None

    # ---------- 游戏逻辑 ----------
    def place_piece(self, col, row):
        if self.winner != EMPTY:
            return False
        if not self.is_valid_pos(col, row):
            return False
        # 围棋模式：走专用逻辑
        if self.game_type == "go":
            success, captured = self._go_place_piece(col, row, self.current_player)
            if not success:
                self.toast_message = "禁入点或劫争，不可落子"
                self.toast_expire = pygame.time.get_ticks() + 2000
                return False
            # 记录悔棋所需的元信息
            self.move_history.append((col, row, self.current_player))
            if not hasattr(self, "go_move_meta"):
                self.go_move_meta = []
            self.go_move_meta.append({
                "captured": captured,
                "ko_point": self.go_ko_point,
                "black_caps": self.go_black_captures,
                "white_caps": self.go_white_captures,
                "last_pass": self.go_last_pass,
            })
            self.play_sound(self.place_sound)
            if self.go_black_captures >= 15:
                self.winner = BLACK
                self.go_game_ended = True
                self.flash_timer = pygame.time.get_ticks()
            elif self.go_white_captures >= 15:
                self.winner = WHITE
                self.go_game_ended = True
                self.flash_timer = pygame.time.get_ticks()
            else:
                self.current_player = WHITE if self.current_player == BLACK else BLACK
            return True

        # 五子棋模式
        self.board[row][col] = self.current_player
        self.move_history.append((col, row, self.current_player))
        self.play_sound(self.place_sound)
        line = self.check_winner(col, row, self.current_player)
        if line:
            self.winner = self.current_player
            self.win_line = line
            self.flash_timer = pygame.time.get_ticks()
        else:
            self.current_player = WHITE if self.current_player == BLACK else BLACK
        return True

    def undo(self):
        if not self.move_history:
            self.toast_message = "无法悔棋：棋盘上无棋子"
            self.toast_expire = pygame.time.get_ticks() + 2000
            return
        # 围棋模式走专用悔棋
        if self.game_type == "go":
            self._go_undo()
            return
        steps = 2 if self.game_mode == "pve" else 1
        for _ in range(steps):
            if not self.move_history:
                break
            col, row, player = self.move_history.pop()
            self.board[row][col] = EMPTY
            self.current_player = player
        # 撤销后重置胜负状态及 AI 标记
        self.winner = EMPTY
        self.win_line = []
        self.flash_timer = 0
        self.ai_thinking = False

    def reset(self):
        self.board = [[EMPTY for _ in range(BOARD_SIZE)] for _ in range(BOARD_SIZE)]
        self.move_history.clear()
        self.current_player = BLACK
        self.winner = EMPTY
        self.win_line = []
        self.flash_timer = 0
        self.ai_thinking = False
        self.ai_move_at = 0
        self.toast_message = ""
        self.toast_expire = 0
        # 围棋状态重置
        self.go_black_captures = 0
        self.go_white_captures = 0
        self.go_ko_point = None
        self.go_prev_board_hash = ""
        self.go_prev_capture_count = 0
        self.go_pass_count = 0
        self.go_last_pass = None
        self.go_board_history = []
        self.go_game_ended = False
        if hasattr(self, "go_move_meta"):
            self.go_move_meta.clear()

    # ---------- AI 逻辑 ----------
    @property
    def ai_color(self):
        """AI 的棋子颜色：总是玩家棋色的对立面"""
        return WHITE if self.actual_player_color == BLACK else BLACK

    def _score_line(self, col, row, dx, dy, player):
        count, open_ends = self._scan_direction(col, row, dx, dy, player)
        if count >= 5:   return 100000
        if count == 4:   return 30000 if open_ends == 2 else 8000 if open_ends == 1 else 0
        if count == 3:   return 5000 if open_ends == 2 else 1000 if open_ends == 1 else 0
        if count == 2:   return 500 if open_ends == 2 else 100 if open_ends == 1 else 0
        if count == 1:   return 10 if open_ends == 2 else 1
        return 0

    def ai_decide(self):
        """根据游戏类型和难度等级分发 AI 决策"""
        if self.game_type == "go":
            self._go_ai_decide()
            return
        if self.ai_difficulty == "easy":
            self._ai_easy()
        elif self.ai_difficulty == "hard":
            self._ai_hard()
        else:
            self._ai_medium()

    def _ai_easy(self):
        """简单级 AI：随机选择空位落子"""
        candidates = [(c, r) for r in range(BOARD_SIZE) for c in range(BOARD_SIZE)
                      if self.board[r][c] == EMPTY]
        if candidates:
            self.place_piece(*random.choice(candidates))

    def _ai_medium(self):
        """中等级 AI：优先防守，拦截玩家连子"""
        best_score = -1
        best_move = None
        directions = [(1, 0), (0, 1), (1, 1), (1, -1)]
        p_clr = self.actual_player_color
        a_clr = self.ai_color
        for row in range(BOARD_SIZE):
            for col in range(BOARD_SIZE):
                if self.board[row][col] != EMPTY:
                    continue
                defense = sum(self._score_line(col, row, dx, dy, p_clr)
                            for dx, dy in directions)
                offense = sum(self._score_line(col, row, dx, dy, a_clr)
                            for dx, dy in directions)
                score = defense * 1.1 + offense
                if score > best_score:
                    best_score = score
                    best_move = (col, row)
        if best_move:
            self.place_piece(*best_move)

    def _ai_hard(self):
        """困难级 AI：攻守兼顾 + 中心抢占 + 连子优先级判断"""
        best_score = -1
        best_move = None
        directions = [(1, 0), (0, 1), (1, 1), (1, -1)]
        center = BOARD_SIZE // 2
        p_clr = self.actual_player_color
        a_clr = self.ai_color
        for row in range(BOARD_SIZE):
            for col in range(BOARD_SIZE):
                if self.board[row][col] != EMPTY:
                    continue
                # 攻防评分
                defense = sum(self._score_line(col, row, dx, dy, p_clr)
                            for dx, dy in directions)
                offense = sum(self._score_line(col, row, dx, dy, a_clr)
                            for dx, dy in directions)
                # 中心近距奖励
                dist = math.hypot(col - center, row - center)
                center_bonus = (BOARD_SIZE - dist) * 3
                score = defense * 1.3 + offense * 1.2 + center_bonus
                # 连子优先加成
                if offense >= 30000:
                    score += 50000
                if defense >= 30000:
                    score += 60000
                if score > best_score:
                    best_score = score
                    best_move = (col, row)
        if best_move:
            self.place_piece(*best_move)

    # ========== 围棋规则引擎 ==========
    def _go_neighbors(self, col, row):
        """返回 (col,row) 上下左右四个相邻格（棋盘内）"""
        dirs = [(0, -1), (0, 1), (-1, 0), (1, 0)]
        return [(col + dx, row + dy) for dx, dy in dirs
                if 0 <= col + dx < BOARD_SIZE and 0 <= row + dy < BOARD_SIZE]

    def _go_group(self, col, row, player=None):
        """获取 (col,row) 所在连通棋子群（含自身）"""
        if player is None:
            player = self.board[row][col]
        if player == EMPTY:
            return set()
        group = set()
        stack = [(col, row)]
        while stack:
            c, r = stack.pop()
            if (c, r) in group:
                continue
            if not (0 <= c < BOARD_SIZE and 0 <= r < BOARD_SIZE):
                continue
            if self.board[r][c] != player:
                continue
            group.add((c, r))
            for nc, nr in self._go_neighbors(c, r):
                if (nc, nr) not in group:
                    stack.append((nc, nr))
        return group

    def _go_liberties(self, group):
        """计算棋子群的「气」数 — 相邻空位"""
        liberties = set()
        for c, r in group:
            for nc, nr in self._go_neighbors(c, r):
                if self.board[nr][nc] == EMPTY:
                    liberties.add((nc, nr))
        return liberties

    def _go_capture(self, col, row, player):
        """落子后：检查并移除无气敌方群，返回被提掉的棋子列表 [(c,r,color),...]"""
        captured = []
        opp = WHITE if player == BLACK else BLACK
        for nc, nr in self._go_neighbors(col, row):
            if self.board[nr][nc] != opp:
                continue
            grp = self._go_group(nc, nr, opp)
            if not self._go_liberties(grp):
                for (cc, cr) in grp:
                    captured.append((cc, cr, self.board[cr][cc]))
                    self.board[cr][cc] = EMPTY
        return captured

    def _go_board_hash(self):
        """生成当前棋盘简单哈希（用于劫争检测）"""
        h = []
        for r in range(BOARD_SIZE):
            for c in range(BOARD_SIZE):
                h.append(str(self.board[r][c]))
        return "".join(h)

    def _go_flood_territory(self, visited, col, row):
        """泛洪填充：从空位出发，确定区域归属（仅黑/白/中立）"""
        if not (0 <= col < BOARD_SIZE and 0 <= row < BOARD_SIZE):
            return None, set()
        if visited[row][col]:
            return None, set()
        if self.board[row][col] != EMPTY:
            return None, set()

        region = set()
        stack = [(col, row)]
        borders = set()  # 相邻的棋子颜色

        while stack:
            c, r = stack.pop()
            if c < 0 or c >= BOARD_SIZE or r < 0 or r >= BOARD_SIZE:
                continue
            if visited[r][c]:
                continue
            if self.board[r][c] != EMPTY:
                borders.add(self.board[r][c])
                continue
            visited[r][c] = True
            region.add((c, r))
            for nc, nr in self._go_neighbors(c, r):
                stack.append((nc, nr))

        # 确定归属
        if len(borders) == 1:
            return list(borders)[0], region
        else:  # 0 或 2 种颜色相邻 -> 中立
            return None, region

    def _go_score_territory(self):
        """数目计分（中国规则：地盘 + 棋盘上的活子）"""
        visited = [[False for _ in range(BOARD_SIZE)] for _ in range(BOARD_SIZE)]
        black_territory = 0
        white_territory = 0
        black_stones = 0
        white_stones = 0

        # 统计子数
        for r in range(BOARD_SIZE):
            for c in range(BOARD_SIZE):
                if self.board[r][c] == BLACK:
                    black_stones += 1
                elif self.board[r][c] == WHITE:
                    white_stones += 1

        # 地域统计
        for r in range(BOARD_SIZE):
            for c in range(BOARD_SIZE):
                if self.board[r][c] == EMPTY and not visited[r][c]:
                    owner, region = self._go_flood_territory(visited, c, r)
                    if owner == BLACK:
                        black_territory += len(region)
                    elif owner == WHITE:
                        white_territory += len(region)

        # 中国规则：子空皆地（territory + stones），白方贴目 6.5
        komi = 6.5
        black_total = black_territory + black_stones
        white_total = white_territory + white_stones + komi
        return black_total, white_total, black_territory, white_territory, black_stones, white_stones

    def _go_pass(self, player):
        """围棋 pass：连续双方交替 pass 则结束对局"""
        if self.go_last_pass is not None and self.go_last_pass != player:
            # 对方刚 pass 过，现在我方也 pass → 连续 pass
            self.go_pass_count = 2
        else:
            # 首次 pass 或同一方重复 pass
            self.go_pass_count = 1

        self.go_last_pass = player

        if self.go_pass_count >= 2:
            # 双方连续 pass，进入计分
            self.go_game_ended = True
            blk_total, wht_total, blk_terr, wht_terr, blk_stn, wht_stn = self._go_score_territory()
            if blk_total > wht_total:
                self.winner = BLACK
            elif wht_total > blk_total:
                self.winner = WHITE
            else:
                self.winner = EMPTY  # 平局
            self.flash_timer = pygame.time.get_ticks()
            # 存储计分详情用于显示
            self._go_score_detail = {
                "black_total": blk_total, "white_total": wht_total,
                "black_territory": blk_terr, "white_territory": wht_terr,
                "black_stones": blk_stn, "white_stones": wht_stn,
            }
            return True  # 对局结束

        # 记录悔棋元信息
        self.move_history.append((-1, -1, player))  # 特殊标记表示 pass
        if not hasattr(self, "go_move_meta"):
            self.go_move_meta = []
        self.go_move_meta.append({
            "captured": [],
            "ko_point": self.go_ko_point,
            "black_caps": self.go_black_captures,
            "white_caps": self.go_white_captures,
            "is_pass": True,
            "last_pass": player,
        })
        return False

    def _go_place_piece(self, col, row, player):
        """围棋落子：含禁入/提子/劫争/超级劫/胜负判定，返回 (success, captured_list)"""
        if self.board[row][col] != EMPTY:
            return False, []
        if self.go_game_ended:
            return False, []

        # 试探性落子
        self.board[row][col] = player

        # 1. 提走敌方无气群
        captured = self._go_capture(col, row, player)

        # 2. 自检：落子后我方群是否有气
        own_group = self._go_group(col, row, player)
        if not self._go_liberties(own_group):
            # 如果提掉了对方棋子，则不算自杀
            if not captured:
                self.board[row][col] = EMPTY
                return False, []

        # 3. 基本劫争检测：单子互提
        if len(captured) == 1 and self.go_ko_point == (col, row):
            new_hash = self._go_board_hash()
            if new_hash == self.go_prev_board_hash:
                self.board[row][col] = EMPTY
                for cc, cr, cp in captured:
                    self.board[cr][cc] = cp
                return False, []

        # 4. 位置超级劫：落子后棋盘不能与任何历史状态相同
        new_hash = self._go_board_hash()
        if new_hash in self.go_board_history:
            self.board[row][col] = EMPTY
            for cc, cr, cp in captured:
                self.board[cr][cc] = cp
            return False, []

        # 5. 记录当前棋盘状态到历史（超级劫）
        self.go_board_history.append(self._go_board_hash())
        if len(self.go_board_history) > 200:
            self.go_board_history = self.go_board_history[-200:]

        # 6. 更新捕获计数
        self.go_prev_capture_count = len(captured)
        if player == BLACK:
            self.go_black_captures += len(captured)
        else:
            self.go_white_captures += len(captured)

        # 7. 更新劫争状态：只有单子提才产生劫
        if len(captured) == 1:
            self.go_ko_point = (captured[0][0], captured[0][1])
        else:
            self.go_ko_point = None
        self.go_prev_board_hash = new_hash

        # 8. 重置 pass 计数（落子后 pass 计数清零）
        self.go_pass_count = 0
        self.go_last_pass = None

        return True, captured

    # ---------- 围棋 AI 公用工具 ----------
    def _go_candidate_moves(self, max_dist=3):
        """生成候选落子位置：已有棋子周围 max_dist 格内 + 角星位"""
        candidates = set()
        center = BOARD_SIZE // 2
        # 开局阶段：加入角、星位
        if len(self.move_history) < 6:
            star_pts = [(3, 3), (3, BOARD_SIZE - 4), (BOARD_SIZE - 4, 3),
                        (BOARD_SIZE - 4, BOARD_SIZE - 4),
                        (center, center)]
            for sc, sr in star_pts:
                if self.board[sr][sc] == EMPTY:
                    candidates.add((sc, sr))
        for r in range(BOARD_SIZE):
            for c in range(BOARD_SIZE):
                if self.board[r][c] != EMPTY:
                    for dr in range(-max_dist, max_dist + 1):
                        for dc in range(-max_dist, max_dist + 1):
                            nr, nc = r + dr, c + dc
                            if 0 <= nr < BOARD_SIZE and 0 <= nc < BOARD_SIZE:
                                if self.board[nr][nc] == EMPTY:
                                    candidates.add((nc, nr))
        if not candidates:
            # 全空棋盘：下天元
            candidates.add((center, center))
        return list(candidates)

    def _go_influence_map(self, player, decay=0.85, max_spread=6):
        """计算 player 棋子的影响力地图（指数衰减）"""
        influence = [[0.0 for _ in range(BOARD_SIZE)] for _ in range(BOARD_SIZE)]
        # BFS 扩散
        from collections import deque
        queue = deque()
        for r in range(BOARD_SIZE):
            for c in range(BOARD_SIZE):
                if self.board[r][c] == player:
                    influence[r][c] = 1.0
                    queue.append((c, r, 1))
        # 传播
        visited_origin = [[False for _ in range(BOARD_SIZE)] for _ in range(BOARD_SIZE)]
        for r in range(BOARD_SIZE):
            for c in range(BOARD_SIZE):
                if self.board[r][c] == player:
                    visited_origin[r][c] = True

        while queue:
            c, r, depth = queue.popleft()
            if depth >= max_spread:
                continue
            val = decay ** depth
            for nc, nr in self._go_neighbors(c, r):
                if self.board[nr][nc] != EMPTY:
                    continue
                if influence[nr][nc] < val:
                    influence[nr][nc] = max(influence[nr][nc], val)
                    queue.append((nc, nr, depth + 1))
        return influence

    def _go_count_atari(self, col, row, player):
        """检测落子 (col,row) 后 player 方处于打吃（仅 1 气）的群数量"""
        if self.board[row][col] != player:
            return 0
        count = 0
        opp = WHITE if player == BLACK else BLACK
        # 检查对方相邻群是否被打吃
        checked = set()
        for nc, nr in self._go_neighbors(col, row):
            if self.board[nr][nc] != opp:
                continue
            if (nc, nr) in checked:
                continue
            grp = self._go_group(nc, nr, opp)
            checked.update(grp)
            if len(self._go_liberties(grp)) == 1:
                count += 1
        return count

    def _go_eye_potential(self, col, row, player):
        """粗略估计 (col,row) 是否能形成眼位（用于评估）"""
        if self.board[row][col] != EMPTY:
            return 0
        neighbors = self._go_neighbors(col, row)
        own_count = sum(1 for nc, nr in neighbors if self.board[nr][nc] == player)
        empty_count = sum(1 for nc, nr in neighbors if self.board[nr][nc] == EMPTY)
        total = len(neighbors)  # 2-4 on edges/corners
        if total == 0:
            return 0
        # 大多是己方棋子 + 有些空位 = 可能是眼
        return (own_count / total) * (own_count + empty_count >= total) * 0.5

    def _go_evaluate_move(self, col, row, player):
        """综合评估在 (col,row) 落子的价值（不实际落子，用试探+恢复）"""
        opp = WHITE if player == BLACK else BLACK
        old_board = [r[:] for r in self.board]
        score = 0.0

        # 试探落子
        self.board[row][col] = player
        captured = self._go_capture(col, row, player)

        # 1) 吃子价值
        n_cap = len(captured)
        score += n_cap * n_cap * 120

        # 2) 自身气数
        own_grp = self._go_group(col, row, player)
        own_libs = len(self._go_liberties(own_grp))
        if own_libs == 0 and n_cap == 0:
            # 自杀，废弃
            for r in range(BOARD_SIZE):
                self.board[r] = old_board[r][:]
            return -99999
        score += own_libs * 12

        # 3) 打吃对手
        atari_count = self._go_count_atari(col, row, player)
        score += atari_count * 80

        # 恢复试探前的棋盘
        for r in range(BOARD_SIZE):
            self.board[r] = old_board[r][:]

        # 4) 防吃：对手在此落子能提多少
        self.board[row][col] = opp
        opp_captured = self._go_capture(col, row, opp)
        opp_n = len(opp_captured)
        score += opp_n * opp_n * 80
        for r in range(BOARD_SIZE):
            self.board[r] = old_board[r][:]

        # 5) 中心近距
        center = BOARD_SIZE // 2
        dist = math.hypot(col - center, row - center)
        score += (BOARD_SIZE - dist) * 2.5

        # 6) 眼位评估
        score += self._go_eye_potential(col, row, player) * 25

        # 7) 连接己方棋子
        has_own = any(self.board[nr][nc] == player
                      for nc, nr in self._go_neighbors(col, row))
        if has_own:
            score += 35

        # 8) 影响地图差异（节省计算：仅在分数相近时计算）
        # 此处在后续 hard AI 中单独计算

        return score

    def _go_ai_easy(self):
        """简单级围棋 AI：随机选择合理位置（避开自杀和明显的禁入点）"""
        candidates = self._go_candidate_moves(max_dist=2)
        if not candidates:
            candidates = [(c, r) for r in range(BOARD_SIZE) for c in range(BOARD_SIZE)
                          if self.board[r][c] == EMPTY]
        # 过滤自杀
        valid = []
        a_clr = self.ai_color
        for col, row in candidates:
            if self._go_evaluate_move(col, row, a_clr) > -90000:
                valid.append((col, row))
        if valid:
            col, row = random.choice(valid)
            self._go_make_move(col, row)
        else:
            # 无合法移动，pass
            self._go_ai_pass()

    def _go_ai_medium(self):
        """中等级围棋 AI：综合评分 + 局部搜索"""
        a_clr = self.ai_color
        candidates = self._go_candidate_moves(max_dist=3)

        best_score = -1
        best_move = None

        for col, row in candidates:
            score = self._go_evaluate_move(col, row, a_clr)
            if score <= -90000:
                continue
            if score > best_score:
                best_score = score
                best_move = (col, row)

        if best_move:
            self._go_make_move(*best_move)
        else:
            self._go_ai_pass()

    def _go_ai_hard(self):
        """困难级围棋 AI：影响地图 + 局部搜索 + 随机模拟决胜评估"""
        a_clr = self.ai_color
        opp = WHITE if a_clr == BLACK else BLACK
        candidates = self._go_candidate_moves(max_dist=4)

        # 影响地图
        own_inf = self._go_influence_map(a_clr, decay=0.82, max_spread=5)
        opp_inf = self._go_influence_map(opp, decay=0.82, max_spread=5)

        scored = []
        for col, row in candidates:
            score = self._go_evaluate_move(col, row, a_clr)
            if score <= -90000:
                continue

            # 影响地图差异
            inf_diff = own_inf[row][col] - opp_inf[row][col]
            score += inf_diff * 40

            # 角落奖励（早期）
            if len(self.move_history) < 12:
                corner_dist = min(
                    math.hypot(col - 2, row - 2),
                    math.hypot(col - (BOARD_SIZE - 3), row - 2),
                    math.hypot(col - 2, row - (BOARD_SIZE - 3)),
                    math.hypot(col - (BOARD_SIZE - 3), row - (BOARD_SIZE - 3)),
                )
                score += max(0, 12 - corner_dist) * 15

            scored.append((col, row, score))

        if not scored:
            self._go_ai_pass()
            return

        # 按分数排序，取前 N 名候选做随机模拟决胜
        scored.sort(key=lambda x: -x[2])
        top_n = min(25, len(scored))
        top_candidates = scored[:top_n]

        if top_n <= 1:
            self._go_make_move(*top_candidates[0][:2])
            return

        # 轻量随机模拟：对每个候选进行若干次快速随机 rollout
        sims_per = max(15, 400 // top_n)
        sim_results = []
        for col, row, base_score in top_candidates:
            wins = 0
            for _ in range(sims_per):
                if self._go_simulate_rollout(col, row, a_clr):
                    wins += 1
            sim_results.append((col, row, base_score, wins))

        # 综合评分：基础分 + 模拟胜率
        best = max(sim_results, key=lambda x: x[2] + x[3] * 10)
        self._go_make_move(best[0], best[1])

    def _go_simulate_rollout(self, col, row, player, max_steps=14):
        """快速随机模拟：在 (col,row) 落子后，双方随机走几步，判断己方优势"""
        opp = WHITE if player == BLACK else BLACK
        saved_board = [r[:] for r in self.board]
        saved_caps_b = self.go_black_captures
        saved_caps_w = self.go_white_captures

        # 落子
        self.board[row][col] = player
        self._go_capture(col, row, player)

        # 随机交替走几步
        sim_board = [r[:] for r in self.board]
        current = opp  # 对手回合
        for step in range(max_steps):
            # 找所有合法空位
            empties = [(c, r) for r in range(BOARD_SIZE) for c in range(BOARD_SIZE)
                       if sim_board[r][c] == EMPTY]
            if not empties:
                break
            # 随机选择
            mc, mr = random.choice(empties)
            # 快速试探（用简化版检查）
            sim_board[mr][mc] = current
            # 检查是否自杀 - 跳过
            grp = set()
            stack = [(mc, mr)]
            while stack:
                c2, r2 = stack.pop()
                if (c2, r2) in grp:
                    continue
                if not (0 <= c2 < BOARD_SIZE and 0 <= r2 < BOARD_SIZE):
                    continue
                if sim_board[r2][c2] != current:
                    continue
                grp.add((c2, r2))
                for nc, nr in self._go_neighbors(c2, r2):
                    stack.append((nc, nr))
            has_liberty = any(
                sim_board[nr2][nc2] == EMPTY
                for gc, gr_ in grp
                for nc2, nr2 in self._go_neighbors(gc, gr_)
            )
            if not has_liberty:
                sim_board[mr][mc] = EMPTY
                continue

            current = WHITE if current == BLACK else BLACK

        # 评估终局：计算各方有效棋子数（粗略）
        own_count = sum(1 for r in range(BOARD_SIZE) for c in range(BOARD_SIZE)
                        if sim_board[r][c] == player)
        opp_count = sum(1 for r in range(BOARD_SIZE) for c in range(BOARD_SIZE)
                        if sim_board[r][c] == opp)

        # 恢复原始棋盘
        self.board = saved_board
        self.go_black_captures = saved_caps_b
        self.go_white_captures = saved_caps_w

        return own_count >= opp_count

    def _go_ai_pass(self):
        """AI 选择 pass"""
        player = self.current_player
        if self._go_pass(player):
            return  # 对局结束
        self.play_sound(self.place_sound)
        self.current_player = WHITE if player == BLACK else BLACK

    def _go_ai_decide(self):
        """围棋 AI 调度"""
        if self.ai_difficulty == "easy":
            self._go_ai_easy()
        elif self.ai_difficulty == "hard":
            self._go_ai_hard()
        else:
            self._go_ai_medium()

    def _go_make_move(self, col, row):
        """执行围棋落子并记录元信息用于悔棋"""
        player = self.current_player
        success, captured = self._go_place_piece(col, row, player)
        if not success:
            return
        # 记录悔棋所需信息
        self.move_history.append((col, row, player))
        go_meta = {
            "captured": captured,
            "ko_point": self.go_ko_point,
            "black_caps": self.go_black_captures,
            "white_caps": self.go_white_captures,
            "last_pass": self.go_last_pass,
        }
        if not hasattr(self, "go_move_meta"):
            self.go_move_meta = []
        self.go_move_meta.append(go_meta)
        self.play_sound(self.place_sound)
        # 胜负判定
        if self.go_black_captures >= 15:
            self.winner = BLACK
            self.go_game_ended = True
            self.flash_timer = pygame.time.get_ticks()
        elif self.go_white_captures >= 15:
            self.winner = WHITE
            self.go_game_ended = True
            self.flash_timer = pygame.time.get_ticks()
        else:
            self.current_player = WHITE if player == BLACK else BLACK

    def _go_handle_pass(self):
        """处理玩家 Pass（在玩家回合时调用）"""
        if self.game_type != "go" or self.winner != EMPTY or self.go_game_ended:
            return
        # PVE 模式：必须是玩家回合
        if self.game_mode == "pve" and self.current_player != self.actual_player_color:
            return
        player = self.current_player
        game_over = self._go_pass(player)
        self.play_sound(self.place_sound)
        if game_over:
            # 显示数目计分结果
            if self._go_score_detail:
                sd = self._go_score_detail
                winner_name = "黑棋" if self.winner == BLACK else "白棋" if self.winner == WHITE else "双方"
                if self.winner == EMPTY:
                    self.toast_message = f"数目计分：平局！"
                else:
                    self.toast_message = f"{winner_name}胜！黑{sd['black_total']:.1f} vs 白{sd['white_total']:.1f}"
                self.toast_expire = pygame.time.get_ticks() + 5000
            return
        # 显示 pass 提示
        self.toast_message = f"{'黑棋' if player == BLACK else '白棋'} Pass ({self.go_pass_count}/2)"
        self.toast_expire = pygame.time.get_ticks() + 2000
        self.current_player = WHITE if player == BLACK else BLACK



    def _go_undo(self):
        """围棋悔棋：恢复上一步（含 pass）"""
        if not self.move_history or not hasattr(self, "go_move_meta") or not self.go_move_meta:
            self.toast_message = "无法悔棋：棋盘上无棋子"
            self.toast_expire = pygame.time.get_ticks() + 2000
            return
        steps = 2 if self.game_mode == "pve" else 1
        for _ in range(steps):
            if not self.move_history or not self.go_move_meta:
                break
            col, row, player = self.move_history.pop()
            meta = self.go_move_meta.pop()

            if meta.get("is_pass"):
                # 撤销 pass
                self.go_pass_count = max(0, self.go_pass_count - 1)
                if self.go_move_meta:
                    self.go_last_pass = self.go_move_meta[-1].get("last_pass", None)
                else:
                    self.go_last_pass = None
            else:
                # 撤销实际落子
                self.board[row][col] = EMPTY
                # 还原被提了的棋子
                for cc, cr, cp in meta["captured"]:
                    self.board[cr][cc] = cp
                # 重算 pass_count
                self.go_pass_count = 0

            self.current_player = player
            # 还原得分 & 劫争
            self.go_black_captures = meta.get("black_caps", 0)
            self.go_white_captures = meta.get("white_caps", 0)
            if self.go_move_meta:
                self.go_ko_point = self.go_move_meta[-1].get("ko_point", None)
                self.go_last_pass = self.go_move_meta[-1].get("last_pass", None)
            else:
                self.go_ko_point = None
                self.go_last_pass = None

            # 还原超级劫历史：移除落子添加的哈希
            if not meta.get("is_pass") and self.go_board_history:
                self.go_board_history.pop()

        self.winner = EMPTY
        self.win_line = []
        self.flash_timer = 0
        self.ai_thinking = False
        self.go_game_ended = False
        if hasattr(self, "_go_score_detail"):
            self._go_score_detail = {}

    # ---------- 游戏初始化 ----------
    def _start_game(self):
        """根据菜单选择初始化对局"""
        if self.game_mode == "pve" and self.player_color == "random":
            self.actual_player_color = random.choice([BLACK, WHITE])
        elif self.game_mode == "pve" and self.player_color == "black":
            self.actual_player_color = BLACK
        elif self.game_mode == "pve":
            self.actual_player_color = WHITE
        else:
            self.actual_player_color = BLACK  # PVP 无意义，黑棋先行
        self.reset()
        self.game_state = "playing"
        # 围棋 PVE：若 AI 执黑则 AI 先走
        if self.game_type == "go" and self.game_mode == "pve":
            if self.actual_player_color == WHITE:
                self.ai_thinking = True
                self.ai_move_at = pygame.time.get_ticks() + 300

    # ===================== 绘制 =====================

    def draw_board(self):
        """棋盘：榧木色柔化多层木框 + 网格 + 星位 + 坐标"""
        border_pad = BOARD_MARGIN - 4
        fx = self.board_origin_x - border_pad
        fy = self.board_origin_y - border_pad
        fw = BOARD_PIXEL + border_pad * 2
        fh = BOARD_PIXEL + border_pad * 2

        # 外框投影
        shadow_rect = pygame.Rect(fx - 3, fy + 2, fw + 18, fh + 18)
        pygame.draw.rect(self.screen, (140, 110, 70, 120), shadow_rect, border_radius=8)

        # 第1层：外框
        outer_rect = pygame.Rect(fx - 6, fy - 6, fw + 12, fh + 12)
        pygame.draw.rect(self.screen, FRAME_OUTER, outer_rect, border_radius=6)

        # 第2层：中框
        mid_rect = pygame.Rect(fx - 3, fy - 3, fw + 6, fh + 6)
        pygame.draw.rect(self.screen, FRAME_MID, mid_rect, border_radius=4)

        # 第3层：内框
        inner_rect = pygame.Rect(fx, fy, fw, fh)
        pygame.draw.rect(self.screen, FRAME_INNER, inner_rect, border_radius=3)

        # 第4层：棋盘面 + 细微纹理线
        board_face = pygame.Rect(fx + 3, fy + 3, fw - 6, fh - 6)
        pygame.draw.rect(self.screen, BOARD_COLOR, board_face)
        pygame.draw.rect(self.screen, LINE_COLOR, board_face, 1)

        # 四角装饰铆钉
        nail_r = 4
        nail_color = (155, 120, 70)
        nail_light = (210, 185, 140)
        corners = [
            (fx + 10, fy + 10),
            (fx + fw - 10, fy + 10),
            (fx + 10, fy + fh - 10),
            (fx + fw - 10, fy + fh - 10),
        ]
        for cx, cy in corners:
            pygame.draw.circle(self.screen, nail_color, (cx, cy), nail_r)
            pygame.draw.circle(self.screen, nail_light, (cx - 1, cy - 1), nail_r - 2)

        # 网格线
        for i in range(BOARD_SIZE):
            sx, sy = self.grid_to_pixel(0, i)
            ex, ey = self.grid_to_pixel(BOARD_SIZE - 1, i)
            pygame.draw.line(self.screen, LINE_COLOR, (sx, sy), (ex, ey), 1)
            sx, sy = self.grid_to_pixel(i, 0)
            ex, ey = self.grid_to_pixel(i, BOARD_SIZE - 1)
            pygame.draw.line(self.screen, LINE_COLOR, (sx, sy), (ex, ey), 1)

        # 星位（15路围棋标准9星位）
        c7 = BOARD_SIZE // 2  # 7
        c3 = 3
        c11 = BOARD_SIZE - 4  # 11
        star_points = [(c3, c3), (c3, c7), (c3, c11),
                       (c7, c3), (c7, c7), (c7, c11),
                       (c11, c3), (c11, c7), (c11, c11)]
        for col, row in star_points:
            px, py = self.grid_to_pixel(col, row)
            pygame.draw.circle(self.screen, LINE_COLOR, (px, py), 5)
            pygame.draw.circle(self.screen, (155, 128, 90), (px, py), 3)

        # 行列标注
        for i, ch in enumerate([chr(ord("A") + i) for i in range(BOARD_SIZE)]):
            px, _ = self.grid_to_pixel(i, 0)
            label = self.font_label.render(ch, True, TEXT_LIGHT)
            self.screen.blit(label, (px - label.get_width() // 2, fy - label.get_height() - 6))
            self.screen.blit(label, (px - label.get_width() // 2, fy + fh + 6))
        for i in range(BOARD_SIZE):
            _, py = self.grid_to_pixel(0, i)
            label = self.font_label.render(str(BOARD_SIZE - i), True, TEXT_LIGHT)
            self.screen.blit(label, (fx - label.get_width() - 6, py - label.get_height() // 2))
            self.screen.blit(label, (fx + fw + 6, py - label.get_height() // 2))

    def draw_piece_at(self, col, row, player, alpha=255):
        """绘制单枚棋子：投影 + 3D 渐变主体"""
        px, py = self.grid_to_pixel(col, row)

        # 柔和投影（预缓存）
        self.screen.blit(self._piece_shadow, (px - PIECE_RADIUS - 3, py - PIECE_RADIUS - 3))

        # 棋子 3D 主体
        if player == BLACK:
            surf = self._piece_black.copy()
        else:
            surf = self._piece_white.copy()

        if alpha < 255:
            surf.set_alpha(alpha)
        self.screen.blit(surf, (px - PIECE_RADIUS, py - PIECE_RADIUS))

    def draw_pieces(self):
        for row in range(BOARD_SIZE):
            for col in range(BOARD_SIZE):
                if self.board[row][col] != EMPTY:
                    self.draw_piece_at(col, row, self.board[row][col])

    def draw_hover(self, mouse_pos):
        if self.winner != EMPTY:
            return
        col, row = self.pixel_to_grid(*mouse_pos)
        if self.is_valid_pos(col, row):
            self.draw_piece_at(col, row, self.current_player, alpha=90)

    def draw_win_line(self):
        """高亮获胜连线：呼吸光晕 + 连线"""
        if not self.win_line:
            return
        elapsed = pygame.time.get_ticks() - self.flash_timer
        alpha = int(140 + 115 * math.sin(elapsed * 0.006))
        alpha = max(70, min(255, alpha))

        # 每颗棋子的光晕
        for col, row in self.win_line:
            px, py = self.grid_to_pixel(col, row)
            glow_size = PIECE_RADIUS + 6
            glow = self._glow_template.copy()
            glow.set_alpha(alpha)
            self.screen.blit(glow, (px - glow_size, py - glow_size))

        # 连线 — 根据 p1/p2 实际位置在 surface 上定位
        (c1, r1), (c2, r2) = self.win_line[0], self.win_line[-1]
        p1 = self.grid_to_pixel(c1, r1)
        p2 = self.grid_to_pixel(c2, r2)
        sx, sy = min(p1[0], p2[0]) - 4, min(p1[1], p2[1]) - 4
        sw = abs(p2[0] - p1[0]) + 8
        sh = abs(p2[1] - p1[1]) + 8
        line_surf = pygame.Surface((sw, sh), pygame.SRCALPHA)
        pygame.draw.line(line_surf, HIGHLIGHT_COLOR + (min(255, alpha + 40),),
                         (p1[0] - sx, p1[1] - sy), (p2[0] - sx, p2[1] - sy), 4)
        self.screen.blit(line_surf, (sx, sy))

    def draw_hud(self, mouse_pos):
        """右侧面板：分块卡片布局，简洁优雅"""
        px = PANEL_LEFT + PANEL_PAD
        pw = PANEL_WIDTH - PANEL_PAD * 2

        # 面板底色
        pygame.draw.rect(self.screen, PANEL_BG, self.panel_rect)
        # 柔化分隔线
        pygame.draw.line(self.screen, (195, 175, 145),
                         (PANEL_LEFT, 0), (PANEL_LEFT, WINDOW_HEIGHT), 2)

        y = 28

        # ---- 标题 ----
        title_txt = "五子棋" if self.game_type == "gobang" else "围  棋"
        title = self.font_title.render(title_txt, True, TEXT_COLOR)
        self.screen.blit(title, (px + (pw - title.get_width()) // 2, y))
        y += title.get_height() + 6
        # 装饰线
        line_y = y
        pygame.draw.line(self.screen, (180, 145, 105), (px + 15, line_y), (px + pw - 15, line_y), 1)
        y += 1
        pygame.draw.line(self.screen, (210, 180, 145), (px + 30, line_y + 1), (px + pw - 30, line_y + 1), 1)
        y += 16

        # ---- 对战模式卡 ----
        mode_text = "人机对战" if self.game_mode == "pve" else "双人对战"
        y = self._draw_card(px, pw, y, 34, None,
                            [("模式", self.font_hint, TEXT_LIGHT),
                             (mode_text, self.font_info, TEXT_COLOR)])
        # PVE 时显示难度和玩家颜色
        if self.game_mode == "pve":
            diff_map = {"easy": "简单", "medium": "中等", "hard": "困难"}
            diff_text = diff_map.get(self.ai_difficulty, "中等")
            clr_map = {"black": "执黑", "white": "执白", "random": "随机"}
            clr_text = clr_map.get(self.player_color, "随机")
            y = self._draw_card(px, pw, y, 34, None,
                                [("难度 / 先后手", self.font_hint, TEXT_LIGHT),
                                 (f"{diff_text} · {clr_text}", self.font_info, TEXT_COLOR)])

        y += 10

        # ---- 回合状态卡 ----
        is_win = self.winner != EMPTY
        bg_card = (255, 242, 232) if is_win else (252, 245, 233)
        border_card = ACCENT_COLOR if is_win else (185, 155, 115)
        y = self._draw_card(px, pw, y, 72, border_card,
                            [("当前回合", self.font_hint, TEXT_LIGHT)],
                            bg=bg_card)
        # 回合指示图标 + 文字（覆盖在卡内）
        y_icon = y - 72 + 24
        if is_win:
            if self.game_type == "go":
                turn_str = "黑棋胜利" if self.winner == BLACK else "白棋胜利"
            else:
                turn_str = "黑棋胜利" if self.winner == BLACK else "白棋胜利"
            turn_color = ACCENT_COLOR
        else:
            turn_str = "黑棋回合" if self.current_player == BLACK else "白棋回合"
            turn_color = TEXT_COLOR
        is_black = (self.winner if is_win else self.current_player) == BLACK
        icon = self._icon_black if is_black else self._icon_white
        self.screen.blit(icon, (px + 14, y_icon))
        turn_label = self.font_info.render(turn_str, True, turn_color)
        self.screen.blit(turn_label, (px + 50, y_icon + 3))

        y += 12
        # 分隔
        pygame.draw.line(self.screen, (215, 190, 155), (px + 10, y), (px + pw - 10, y), 1)
        y += 14

        # ---- 对局统计 ----
        self.screen.blit(self.font_hint.render("对局统计", True, TEXT_LIGHT), (px, y))
        y += 20

        if self.game_type == "go":
            # 围棋：显示提子得分 + Pass 计数
            total = sum(1 for _, _, p in self.move_history if p != -1)  # 不含 pass
            for label, val in [("手数", str(total)),
                               ("黑方提子", str(self.go_black_captures)),
                               ("白方提子", str(self.go_white_captures))]:
                lf = self.font_hint.render(label, True, TEXT_LIGHT)
                vf = self.font_hint.render(val, True, TEXT_COLOR)
                self.screen.blit(lf, (px + 8, y))
                self.screen.blit(vf, (px + pw - vf.get_width() - 8, y))
                y += 20

            # Pass 计数提示
            if self.go_pass_count > 0:
                pass_text = f"连续 Pass: {self.go_pass_count}/2"
                pass_color = ACCENT_COLOR if self.go_pass_count >= 2 else TEXT_LIGHT
                pl = self.font_hint.render(pass_text, True, pass_color)
                self.screen.blit(pl, (px + 8, y))
                y += 20

            # 进度条显示提子得分
            y += 2
            max_pts = 15
            bar_h = 10
            bar_w = pw - 16
            bar_x = px + 8
            pygame.draw.rect(self.screen, (200, 180, 150), (bar_x, y, bar_w, bar_h), border_radius=5)
            bw = int(bar_w * self.go_black_captures / max_pts)
            ww = int(bar_w * self.go_white_captures / max_pts)
            if bw > 0:
                pygame.draw.rect(self.screen, (55, 42, 35), (bar_x, y, bw, bar_h), border_radius=5)
            if ww > 0:
                pygame.draw.rect(self.screen, (210, 200, 185), (bar_x, y, ww, bar_h), border_radius=5)
            pygame.draw.rect(self.screen, (130, 105, 70), (bar_x, y, bar_w, bar_h), 1, border_radius=5)
            y += bar_h + 4
            # 目标分标注
            goal_l = self.font_label.render(f"目标: {max_pts} 提子", True, TEXT_LIGHT)
            self.screen.blit(goal_l, (px + bar_w - goal_l.get_width(), y))
            y += 18

            # 数目计分详情（对局结束后显示）
            if self.go_game_ended and self._go_score_detail:
                sd = self._go_score_detail
                y += 2
                pygame.draw.line(self.screen, (215, 190, 155), (px + 10, y), (px + pw - 10, y), 1)
                y += 10
                score_title = self.font_hint.render("数目计分", True, TEXT_COLOR)
                self.screen.blit(score_title, (px, y))
                y += 20
                for label, val in [
                    (f"黑方: 地盘{sd['black_territory']}+子{sd['black_stones']}",
                     f"{sd['black_total']:.1f}"),
                    (f"白方: 地盘{sd['white_territory']}+子{sd['white_stones']}+贴目6.5",
                     f"{sd['white_total']:.1f}"),
                ]:
                    lf = self.font_label.render(label, True, TEXT_LIGHT)
                    vf = self.font_label.render(val, True, ACCENT_COLOR)
                    self.screen.blit(lf, (px + 8, y))
                    self.screen.blit(vf, (px + pw - vf.get_width() - 8, y))
                    y += 18
        else:
            total = len(self.move_history)
            black_n = sum(1 for _, _, p in self.move_history if p == BLACK)
            white_n = sum(1 for _, _, p in self.move_history if p == WHITE)
            for label, val in [("总步数", str(total)), ("黑子", str(black_n)), ("白子", str(white_n))]:
                lf = self.font_hint.render(label, True, TEXT_LIGHT)
                vf = self.font_hint.render(val, True, TEXT_COLOR)
                self.screen.blit(lf, (px + 8, y))
                self.screen.blit(vf, (px + pw - vf.get_width() - 8, y))
                y += 20

        y += 6
        pygame.draw.line(self.screen, (215, 190, 155), (px + 10, y), (px + pw - 10, y), 1)
        y += 14

        # ---- 操作按钮 ----
        self.screen.blit(self.font_hint.render("快捷操作", True, TEXT_LIGHT), (px, y))
        y += 22

        for btn in self.panel_buttons:
            # 跳过围棋专用按钮（非围棋模式或对局已结束）
            if btn.get("go_only") and self.game_type != "go":
                continue
            if btn.get("action") == "pass_go" and self.winner != EMPTY:
                continue
            r = btn["rect"]
            is_hover = r.collidepoint(mouse_pos)
            # 按钮阴影
            shadow_r = pygame.Rect(r.x + 1, r.y + 2, r.w, r.h)
            pygame.draw.rect(self.screen, BUTTON_SHADOW, shadow_r, border_radius=20)
            # 按钮主体
            bg = BUTTON_HOVER if is_hover else BUTTON_BG
            pygame.draw.rect(self.screen, bg, r, border_radius=20)
            pygame.draw.rect(self.screen, BUTTON_BORDER, r, 1, border_radius=20)
            # 悬停内高光
            if is_hover:
                inner = pygame.Rect(r.x + 2, r.y + 2, r.w - 4, r.h // 2 - 2)
                pygame.draw.rect(self.screen, (240, 220, 190, 80), inner, border_radius=16)
            label = self.font_hint.render(btn["text"], True, TEXT_COLOR)
            self.screen.blit(label,
                             (r.x + (r.w - label.get_width()) // 2,
                              r.y + (r.h - label.get_height()) // 2))

    def _draw_card(self, px, pw, y, h, border_color, text_items, bg=None):
        """绘制一张小卡片：圆角矩形 + 文字"""
        if bg is None:
            bg = (248, 240, 228)
        rect = pygame.Rect(px, y, pw, h)
        pygame.draw.rect(self.screen, bg, rect, border_radius=7)
        if border_color:
            pygame.draw.rect(self.screen, border_color, rect, 1, border_radius=7)
        # 文字（如"模式"标签 + 值）
        if len(text_items) == 2:
            l_text, l_font, l_color = text_items[0]
            r_text, r_font, r_color = text_items[1]
            ll = l_font.render(l_text, True, l_color)
            rl = r_font.render(r_text, True, r_color)
            self.screen.blit(ll, (px + 12, y + (h - ll.get_height()) // 2))
            self.screen.blit(rl, (px + pw - rl.get_width() - 12, y + (h - rl.get_height()) // 2))
        else:
            for i, (txt, font, clr) in enumerate(text_items):
                label = font.render(txt, True, clr)
                self.screen.blit(label, (px + 12, y + 10 + i * 22))
        return y + h + 2

    def draw_victory_banner(self):
        """胜利横幅：脉冲缩放动画 + 多层光晕 + 装饰粒子"""
        if self.winner == EMPTY:
            return

        bw = BOARD_AREA_WIDTH
        bh = 64
        bx = 0
        by = BOARD_TOP
        elapsed = pygame.time.get_ticks() - self.flash_timer

        # 背景条
        banner_bg = pygame.Surface((bw, bh), pygame.SRCALPHA)
        banner_bg.fill((25, 12, 5, 230))
        self.screen.blit(banner_bg, (bx, by))
        # 底部金线
        pygame.draw.line(self.screen, (255, 195, 70),
                         (bx + 20, by + bh - 1), (bx + bw - 20, by + bh - 1), 2)

        # 文字内容
        if self.game_type == "go" and self.go_game_ended and self._go_score_detail:
            sd = self._go_score_detail
            if self.winner == BLACK:
                text = f"黑棋胜利 ({sd['black_total']:.1f} : {sd['white_total']:.1f})"
            elif self.winner == WHITE:
                text = f"白棋胜利 ({sd['white_total']:.1f} : {sd['black_total']:.1f})"
            else:
                text = f"双方平局 ({sd['black_total']:.1f} : {sd['white_total']:.1f})"
        else:
            text = "黑棋胜利" if self.winner == BLACK else "白棋胜利"
        cx = bx + bw // 2
        cy = by + bh // 2

        # ---- 脉冲缩放动画 ----
        scale = 1.0 + 0.06 * math.sin(elapsed * 0.005)  # 1.0 ~ 1.06

        # 光晕底色（文字后面）
        glow_size = int(180 * scale)
        glow_surf = pygame.Surface((glow_size + 20, glow_size + 20), pygame.SRCALPHA)
        glow_alpha = int(35 + 20 * math.sin(elapsed * 0.008))
        for rng in range(glow_size // 4, glow_size // 2, 4):
            a = max(0, glow_alpha - rng // 3)
            pygame.draw.circle(glow_surf, (255, 200, 70, a),
                               (glow_surf.get_width() // 2, glow_surf.get_height() // 2), rng)
        self.screen.blit(glow_surf, (cx - glow_surf.get_width() // 2, cy - glow_surf.get_height() // 2))

        # 按比例缩放文字
        base_text = self.font_banner.render(text, True, (255, 210, 55))
        sw = int(base_text.get_width() * scale)
        sh = int(base_text.get_height() * scale)
        if sw > 0 and sh > 0:
            scaled_text = pygame.transform.smoothscale(base_text, (sw, sh))
        else:
            scaled_text = base_text

        # 阴影
        shadow_text = self.font_banner.render(text, True, (15, 8, 0))
        ssw = int(shadow_text.get_width() * scale)
        ssh = int(shadow_text.get_height() * scale)
        if ssw > 0 and ssh > 0:
            scaled_shadow = pygame.transform.smoothscale(shadow_text, (ssw, ssh))
        else:
            scaled_shadow = shadow_text

        self.screen.blit(scaled_shadow,
                         (cx - scaled_shadow.get_width() // 2 + 3,
                          cy - scaled_shadow.get_height() // 2 + 3))
        self.screen.blit(scaled_text,
                         (cx - scaled_text.get_width() // 2,
                          cy - scaled_text.get_height() // 2))

        # ---- 左右装饰星 ----
        star_phase = elapsed * 0.004
        for side in [-1, 1]:
            star_dist = scaled_text.get_width() // 2 + 28
            s_alpha = int(140 + 115 * math.sin(star_phase + side * 1.2))
            s_alpha = max(50, min(255, s_alpha))
            star_scale = 1.0 + 0.12 * math.sin(star_phase + side * 2.0)
            star_label = self.font_info.render("✦", True,
                                                (255, 220, 80) if s_alpha > 160 else (255, 180, 50))
            star_label.set_alpha(s_alpha)
            self.screen.blit(star_label,
                             (cx + side * star_dist - star_label.get_width() // 2,
                              cy - star_label.get_height() // 2))

    def _render_icon_piece(self, color, size=24):
        """小指示棋子：简易 3D（用于预缓存）"""
        r = size // 2
        s = pygame.Surface((size, size), pygame.SRCALPHA)
        # 渐变主体
        for dx in range(size):
            for dy in range(size):
                dist = math.hypot(dx - r, dy - r)
                if dist > r - 1:
                    continue
                t_val = dist / (r - 1)
                factor = 1 - t_val ** 1.5
                if color == BLACK_PIECE_BASE:
                    cr = int(35 + factor * 80)
                    cg = int(30 + factor * 65)
                    cb = int(28 + factor * 55)
                else:
                    cr = int(248 - (1 - factor) * 50)
                    cg = int(245 - (1 - factor) * 53)
                    cb = int(238 - (1 - factor) * 50)
                s.set_at((dx, dy), (cr, cg, cb, 255))
        # 小高光
        pygame.draw.circle(s, (255, 255, 255, 130), (r - 3, r - 3), r // 3)
        return s

    # ---------- Toast 提示 ----------
    def draw_toast(self, now):
        """棋盘中央短暂提示文字，带淡入淡出"""
        if not self.toast_message or now > self.toast_expire:
            return
        remaining = self.toast_expire - now
        alpha = 255
        if remaining < 500:
            alpha = int(255 * remaining / 500)
        if alpha <= 0:
            return

        # 半透明背景条
        bw = 420
        bh = 44
        bx = (BOARD_AREA_WIDTH - bw) // 2
        by = (BOARD_PIXEL - bh) // 2 + BOARD_TOP + BOARD_MARGIN
        bg_alpha = min(220, alpha)
        bg_surf = pygame.Surface((bw, bh), pygame.SRCALPHA)
        bg_surf.fill((20, 12, 5, bg_alpha))
        self.screen.blit(bg_surf, (bx, by))
        # 底部细线
        line_surf = pygame.Surface((bw - 40, 2), pygame.SRCALPHA)
        line_surf.fill((255, 195, 70, bg_alpha // 2))
        self.screen.blit(line_surf, (bx + 20, by + bh - 2))

        # 文字
        label = self.font_info.render(self.toast_message, True, (245, 225, 180))
        label.set_alpha(alpha)
        self.screen.blit(label, (bx + (bw - label.get_width()) // 2,
                                 by + (bh - label.get_height()) // 2))

    # ---------- 菜单绘制 ----------
    def draw_menu(self, mouse_pos):
        """预游戏菜单：游戏类型 / 模式 / 难度 / 先后手选择"""
        self.screen.fill(BG_COLOR)

        # 棋盘预览（淡化）
        self.draw_board()

        # 半透明遮罩
        overlay = pygame.Surface((WINDOW_WIDTH, WINDOW_HEIGHT), pygame.SRCALPHA)
        overlay.fill((250, 243, 230, 160))
        self.screen.blit(overlay, (0, 0))

        # 标题
        title_txt = "五子棋" if self.game_type == "gobang" else "围  棋"
        title_label = self.font_menu_title.render(title_txt, True, TEXT_COLOR)
        self.screen.blit(title_label,
                         ((WINDOW_WIDTH - title_label.get_width()) // 2, 88))

        # 副标题
        sub = self.font_hint.render("选择模式与难度，开始对局", True, TEXT_LIGHT)
        self.screen.blit(sub, ((WINDOW_WIDTH - sub.get_width()) // 2, 132))

        cx = WINDOW_WIDTH // 2

        # ---- 游戏类型选择 ----
        type_label = self.font_menu_opt.render("— 游戏类型 —", True, TEXT_LIGHT)
        self.screen.blit(type_label, (cx - type_label.get_width() // 2, 160))

        # ---- 模式选择 ----
        mode_label = self.font_menu_opt.render("— 对战模式 —", True, TEXT_LIGHT)
        self.screen.blit(mode_label, (cx - mode_label.get_width() // 2, 223))

        for btn in self.menu_buttons:
            if btn["group"] == "difficulty" and self.game_mode == "pvp":
                continue
            if btn["group"] == "color" and self.game_mode == "pvp":
                continue
            self._draw_menu_btn(btn, mouse_pos)

        # ---- 难度 & 先后手 标签 ----
        if self.game_mode == "pve":
            diff_label = self.font_menu_opt.render("— AI 难度 —", True, TEXT_LIGHT)
            self.screen.blit(diff_label, (cx - diff_label.get_width() // 2, 298))
            clr_label = self.font_menu_opt.render("— 先后手 —", True, TEXT_LIGHT)
            self.screen.blit(clr_label, (cx - clr_label.get_width() // 2, 390))

        # ---- 底部说明 ----
        if self.game_type == "go":
            hint_txt = "围棋：P 键 Pass · 连续两次 Pass 数目计分 · Z 悔棋  R 重开"
        else:
            hint_txt = "ESC 退出  ·  游戏中可按 Z 悔棋  R 重新开始"
        hint = self.font_hint.render(hint_txt, True, TEXT_LIGHT)
        self.screen.blit(hint, ((WINDOW_WIDTH - hint.get_width()) // 2, WINDOW_HEIGHT - 40))

    def _draw_menu_btn(self, btn, mouse_pos):
        """绘制单个菜单按钮，高亮当前选中项"""
        r = btn["rect"]
        is_hover = r.collidepoint(mouse_pos)
        group = btn["group"]
        value = btn["value"]

        # 判断是否当前选中
        selected = False
        if group == "gametype":
            selected = self.game_type == value
        elif group == "mode":
            selected = self.game_mode == value
        elif group == "difficulty":
            selected = self.ai_difficulty == value
        elif group == "color":
            selected = self.player_color == value

        # 配色
        if selected:
            bg = BUTTON_HOVER
            border = ACCENT_COLOR
        elif is_hover:
            bg = (228, 212, 185)
            border = BUTTON_BORDER
        else:
            bg = (215, 198, 168)
            border = (170, 145, 110)

        # 阴影
        shadow_r = pygame.Rect(r.x + 2, r.y + 3, r.w, r.h)
        pygame.draw.rect(self.screen, (175, 148, 115, 100), shadow_r, border_radius=12)

        # 主体
        pygame.draw.rect(self.screen, bg, r, border_radius=12)
        if selected:
            pygame.draw.rect(self.screen, border, r, 2, border_radius=12)
        else:
            pygame.draw.rect(self.screen, border, r, 1, border_radius=12)

        # 文字
        color = ACCENT_COLOR if selected else TEXT_COLOR
        label = self.font_menu_btn.render(btn["text"], True, color)
        self.screen.blit(label, (r.x + (r.w - label.get_width()) // 2,
                                 r.y + (r.h - label.get_height()) // 2))

    # ===================== 主循环 =====================
    def run(self):
        clock = pygame.time.Clock()
        running = True
        while running:
            mouse_pos = pygame.mouse.get_pos()
            now = pygame.time.get_ticks()

            # ======== 事件处理 ========
            for event in pygame.event.get():
                if event.type == QUIT:
                    running = False
                elif event.type == KEYDOWN:
                    if event.key == K_ESCAPE:
                        if self.game_state == "menu":
                            running = False
                        else:
                            self.game_state = "menu"
                    elif self.game_state == "playing":
                        if event.key == K_r:
                            self.reset()
                        elif event.key == K_z:
                            self.undo()
                        elif event.key == K_p and self.game_type == "go":
                            self._go_handle_pass()
                elif event.type == MOUSEBUTTONDOWN and event.button == 1:
                    click_pos = event.pos

                    # ---- 菜单状态：处理菜单按钮点击 ----
                    if self.game_state == "menu":
                        menus_handled = False
                        for btn in self.menu_buttons:
                            if btn["rect"].collidepoint(click_pos):
                                group = btn["group"]
                                if group == "gametype":
                                    self.game_type = btn["value"]
                                elif group == "mode":
                                    self.game_mode = btn["value"]
                                elif group == "difficulty":
                                    self.ai_difficulty = btn["value"]
                                elif group == "color":
                                    self.player_color = btn["value"]
                                elif group == "start":
                                    self._start_game()
                                menus_handled = True
                                break
                        if menus_handled:
                            continue

                    # ---- 游戏状态：处理面板按钮 + 棋盘落子 ----
                    if self.game_state == "playing":
                        panel_clicked = False
                        for btn in self.panel_buttons:
                            if btn["rect"].collidepoint(click_pos):
                                action = btn["action"]
                                if action == "reset":
                                    self.reset()
                                elif action == "undo":
                                    self.undo()
                                elif action == "quit":
                                    running = False
                                elif action == "to_menu":
                                    self.game_state = "menu"
                                elif action == "pass_go":
                                    self._go_handle_pass()
                                panel_clicked = True
                                break
                        if panel_clicked:
                            continue
                        # 仅在玩家回合允许落子
                        if (self.game_mode == "pve"
                                and self.current_player != self.actual_player_color):
                            continue
                        if self.winner == EMPTY and click_pos[0] < PANEL_LEFT:
                            # 围棋已结束则不再允许落子
                            if self.game_type == "go" and self.go_game_ended:
                                continue
                            col, row = self.pixel_to_grid(*click_pos)
                            self.place_piece(col, row)

            # ======== 菜单状态渲染 ========
            if self.game_state == "menu":
                self.draw_menu(mouse_pos)
                pygame.display.flip()
                clock.tick(60)
                continue

            # ======== 游戏状态：AI 回合调度 ========
            self.screen.fill(BG_COLOR)
            ai_should_act = (self.game_mode == "pve" and self.winner == EMPTY
                             and self.current_player == self.ai_color)
            if ai_should_act:
                if not self.ai_thinking:
                    self.ai_thinking = True
                    # 围棋 AI 延迟稍长，模拟思考
                    if self.game_type == "go":
                        delay = {"easy": 200, "medium": 500, "hard": 700}.get(self.ai_difficulty, 500)
                    else:
                        delay = 180 if self.ai_difficulty == "easy" else 420
                    self.ai_move_at = now + delay
                elif now >= self.ai_move_at:
                    self.ai_decide()
                    self.ai_thinking = False

            # ======== 游戏状态：绘制 ========
            self.draw_board()
            self.draw_pieces()
            if not ai_should_act:
                self.draw_hover(mouse_pos)
            if self.game_type == "gobang":
                self.draw_win_line()
            self.draw_victory_banner()
            self.draw_toast(now)
            self.draw_hud(mouse_pos)

            pygame.display.flip()
            clock.tick(60)

        pygame.quit()
        sys.exit()


# ==================== 入口 ====================
if __name__ == "__main__":
    GobangGame().run()
