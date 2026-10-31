# main.py-- 

### Imports ###
import sys
import time
import random
import threading
import pygame

### Data & Constants ###

# Window Dimensions (Height increased to 780 to fit the bottom notes toolbar)
WINDOW_WIDTH = 600
WINDOW_HEIGHT = 780
FPS = 60

# Grid Dimensions
BOARD_SIZE = 540
CELL_SIZE = BOARD_SIZE // 9
SUBCELL_SIZE = CELL_SIZE // 3
BOARD_OFFSET_X = (WINDOW_WIDTH - BOARD_SIZE) // 2
BOARD_OFFSET_Y = 110

# Difficulty Settings (Number of given clues)
DIFFICULTIES = {
    "Easy": 40,
    "Medium": 32,
    "Hard": 26,
}

# Colors (Catppuccin Mocha-inspired Dark Mode Palette)
COLOR_BG = (30, 30, 46)               # #1e1e2e - Deep dark background
COLOR_PANEL = (40, 42, 58)            # #282a3a - Board background
COLOR_HIGHLIGHT_GROUP = (52, 55, 77)  # Subtle shade for row/col/box
COLOR_HIGHLIGHT_SAME = (72, 65, 108)  # Subtle purple tint for matching numbers
COLOR_SELECTED = (65, 105, 165)       # Soft blue accent for selected cell
COLOR_GRID_THIN = (69, 71, 90)        # Thin inner cell lines
COLOR_GRID_THICK = (166, 173, 200)    # Thick 3x3 box boundaries and border

COLOR_TEXT_GIVEN = (235, 240, 255)    # Crisp off-white for starting numbers
COLOR_TEXT_PLAYER = (137, 180, 250)   # Soft blue accent for player entries
COLOR_TEXT_WRONG = (243, 139, 168)    # Soft coral red for mistakes
COLOR_TEXT_NOTE = (138, 143, 163)     # #8a8fa3 - Subtle gray for pencil marks
COLOR_TEXT_UI = (205, 214, 244)       # UI bar and title text
COLOR_TEXT_MUTED = (147, 153, 178)    # Subtitles and secondary text

COLOR_BTN_BG = (49, 50, 68)           # Standard button fill
COLOR_BTN_HOVER = (69, 71, 90)        # Button hover fill
COLOR_BTN_ACTIVE = (65, 105, 165)     # Active toggle button fill
COLOR_BTN_ACTIVE_HOVER = (82, 125, 190)  # Active toggle button hover fill
COLOR_BTN_BORDER = (137, 180, 250)    # Button border highlight


### Classes ###

#* Sudoku Generator & Solver Logic
class SudokuGenerator:
    """Handles generating full boards, digging holes, and verifying unique solutions."""

    @staticmethod
    def get_candidates(grid, r, c):
        """Return a set of valid numbers (1-9) that do not conflict with row, col, or box."""
        used = set()
        # Row and Column check
        for i in range(9):
            used.add(grid[r][i])
            used.add(grid[i][c])
        # 3x3 Box check
        br, bc = (r // 3) * 3, (c // 3) * 3
        for i in range(br, br + 3):
            for j in range(bc, bc + 3):
                used.add(grid[i][j])
        return set(range(1, 10)) - used

    @classmethod
    def find_best_empty_cell(cls, grid):
        """
        Find the empty cell with the fewest valid candidates (Minimum Remaining Values).
        Speeds up backtracking significantly compared to naive top-to-bottom scanning.
        Returns (row, col, candidates_list) or (None, None, None) if full.
        """
        best_r, best_c, best_candidates = None, None, None
        min_len = 10

        for r in range(9):
            for c in range(9):
                if grid[r][c] == 0:
                    candidates = list(cls.get_candidates(grid, r, c))
                    num_c = len(candidates)
                    if num_c == 0:
                        return r, c, []  # Dead end immediately detected
                    if num_c < min_len:
                        min_len = num_c
                        best_r, best_c, best_candidates = r, c, candidates
                        if min_len == 1:
                            return best_r, best_c, best_candidates
        return best_r, best_c, best_candidates

    @classmethod
    def fill_board(cls, grid):
        """Fill an empty or partial 9x9 grid using randomized backtracking."""
        r, c, candidates = cls.find_best_empty_cell(grid)
        if r is None:
            return True  # No empty cells left; board is complete

        random.shuffle(candidates)
        for val in candidates:
            grid[r][c] = val
            if cls.fill_board(grid):
                return True
            grid[r][c] = 0
        return False

    @classmethod
    def count_solutions(cls, grid, limit=2):
        """
        Count the number of valid solutions for the given grid.
        Stops immediately once the count reaches `limit` (default 2).
        """
        r, c, candidates = cls.find_best_empty_cell(grid)
        if r is None:
            return 1  # Found 1 valid complete solution
        if not candidates:
            return 0  # Dead end

        total_solutions = 0
        for val in candidates:
            grid[r][c] = val
            total_solutions += cls.count_solutions(grid, limit - total_solutions)
            grid[r][c] = 0  # Backtrack cleanly
            if total_solutions >= limit:
                break
        return total_solutions

    @classmethod
    def generate_puzzle(cls, clues_target):
        """
        Generate a valid Sudoku puzzle with a guaranteed single solution.
        Returns (puzzle_grid, solution_grid).
        """
        # 1. Create a completely filled valid board
        solution = [[0] * 9 for _ in range(9)]
        cls.fill_board(solution)

        # 2. Copy the solution to dig holes for the playable puzzle
        puzzle = [row[:] for row in solution]
        positions = [(r, c) for r in range(9) for c in range(9)]
        random.shuffle(positions)

        current_clues = 81
        for r, c in positions:
            if current_clues <= clues_target:
                break

            backup = puzzle[r][c]
            puzzle[r][c] = 0

            # Verify that removing this number doesn't introduce multiple solutions
            test_grid = [row[:] for row in puzzle]
            if cls.count_solutions(test_grid, limit=2) != 1:
                puzzle[r][c] = backup  # Restore clue if uniqueness is lost
            else:
                current_clues -= 1

        return puzzle, solution



#* Board state and logic management

class Board:
    """Manages the grid state, locked clues, player inputs, notes, score, and win checking."""

    def __init__(self, puzzle, solution):
        self.solution = solution
        self.grid = [row[:] for row in puzzle]
        self.given = [[puzzle[r][c] != 0 for c in range(9)] for r in range(9)]
        self.notes = [[set() for _ in range(9)] for _ in range(9)]
        self.selected = (0, 0)
        self.mistakes = 0
        self.score = 0
        self.scored_cells = set()  # Prevents farming +5 on the same cell repeatedly

    def select(self, r, c):
        """Select a cell on the board."""
        if 0 <= r < 9 and 0 <= c < 9:
            self.selected = (r, c)

    def move_selection(self, dr, dc):
        """Move the selection cursor using arrow keys with wrap-around."""
        r, c = self.selected
        self.selected = ((r + dr) % 9, (c + dc) % 9)

    def place_number(self, val):
        """
        Place a number (1-9) into the selected cell if it is not a locked clue.
         + Awards +5 points for a correct placement and deducts -1 for a mistake.
         + If the number is correct, clears the cell's own notes and removes that
          digit from related notes in the same row, column, and 3x3 box.
         + If the number is wrong, leaves notes in other cells untouched.
        """
        r, c = self.selected
        if self.given[r][c]:
            return  # Cannot edit starting clues

        if self.grid[r][c] == val:
            return  # Ignore redundant input of the same number

        self.grid[r][c] = val
        if val != 0:
            if val == self.solution[r][c]:
                # Correct placement: clear this cell's notes and prune peer notes
                self.clear_cell_notes(r, c)
                self.clear_related_notes(r, c, val)
                if (r, c) not in self.scored_cells:
                    self.score += 5
                    self.scored_cells.add((r, c))
            else:
                # Wrong placement: increment mistakes, penalize score, do NOT touch peer notes
                self.mistakes += 1
                self.score -= 1

    def clear_cell(self):
        """Clear the placed value in the selected cell if it is editable (does not restore notes)."""
        r, c = self.selected
        if not self.given[r][c]:
            self.grid[r][c] = 0

#* Notes pencil marks management

    def toggle_note(self, r, c, n):
        """
        Toggle digit `n` (1-9) in `self.notes[r][c]`.
        Ignored if the cell is a starting clue or currently holds a placed number.
        """
        if self.given[r][c] or self.grid[r][c] != 0:
            return
        if n in self.notes[r][c]:
            self.notes[r][c].remove(n)
        else:
            self.notes[r][c].add(n)

    def clear_cell_notes(self, r, c):
        """Remove all notes from cell (r, c)."""
        self.notes[r][c].clear()

    def clear_related_notes(self, r, c, n):
        """Remove digit `n` from notes of every cell in the same row, column, and 3x3 box."""
        for i in range(9):
            self.notes[r][i].discard(n)
            self.notes[i][c].discard(n)

        br, bc = (r // 3) * 3, (c // 3) * 3
        for i in range(br, br + 3):
            for j in range(bc, bc + 3):
                self.notes[i][j].discard(n)

    def auto_fill_notes(self):
        """
        For every empty cell (grid[r][c] == 0), overwrite its note set with all digits 1-9
        that do not conflict with numbers currently placed in its row, column, and 3x3 box.
        """
        for r in range(9):
            for c in range(9):
                if self.grid[r][c] == 0 and not self.given[r][c]:
                    self.notes[r][c] = SudokuGenerator.get_candidates(self.grid, r, c)
                else:
                    self.notes[r][c].clear()

    def clear_all_notes(self):
        """Remove all notes from every cell on the board."""
        for r in range(9):
            for c in range(9):
                self.notes[r][c].clear()


    def is_cell_wrong(self, r, c):
        """Return True if a cell has a non-zero number that disagrees with the solution."""
        val = self.grid[r][c]
        return val != 0 and val != self.solution[r][c]

    def check_win(self):
        """Return True if all 81 cells are filled and match the solution."""
        for r in range(9):
            for c in range(9):
                if self.grid[r][c] != self.solution[r][c]:
                    return False
        return True



class Button:
    """Interactive UI button with hover and active toggle state support."""

    def __init__(self, x, y, w, h, text, action=None):
        self.rect = pygame.Rect(x, y, w, h)
        self.text = text
        self.action = action
        self.hovered = False
        self.active = False

    def update(self, mouse_pos):
        self.hovered = self.rect.collidepoint(mouse_pos)

    def draw(self, surface, font):
        if self.active:
            bg_color = COLOR_BTN_ACTIVE_HOVER if self.hovered else COLOR_BTN_ACTIVE
            txt_color = COLOR_TEXT_GIVEN
        else:
            bg_color = COLOR_BTN_HOVER if self.hovered else COLOR_BTN_BG
            txt_color = COLOR_TEXT_UI

        pygame.draw.rect(surface, bg_color, self.rect, border_radius=8)
        border_w = 3 if self.active else 2
        pygame.draw.rect(surface, COLOR_BTN_BORDER, self.rect, width=border_w, border_radius=8)

        txt_surf = font.render(self.text, True, txt_color)
        txt_rect = txt_surf.get_rect(center=self.rect.center)
        surface.blit(txt_surf, txt_rect)



class Game:
    """Manages the Pygame lifecycle, screens, background generation, and drawing."""

    def __init__(self):
        pygame.init()
        pygame.display.set_caption("Sudoku")
        self.screen = pygame.display.set_mode((WINDOW_WIDTH, WINDOW_HEIGHT))
        self.clock = pygame.time.Clock()

        # Load clean sans-serif fonts
        font_names = "segoeui,arial,helvetica,dejavusans,sans-serif"
        self.font_title = pygame.font.SysFont(font_names, 48, bold=True)
        self.font_subtitle = pygame.font.SysFont(font_names, 20)
        self.font_cell = pygame.font.SysFont(font_names, 34, bold=True)
        # Note font ~38% of the 34px main cell font size (13px)
        self.font_note = pygame.font.SysFont(font_names, 13, bold=True)
        self.font_ui = pygame.font.SysFont(font_names, 19, bold=True)
        self.font_badge = pygame.font.SysFont(font_names, 13, bold=True)
        self.font_btn = pygame.font.SysFont(font_names, 20, bold=True)
        self.font_hint = pygame.font.SysFont(font_names, 16)

        # State tracking: "MENU", "GENERATING", "PLAYING", "WIN"
        self.state = "MENU"
        self.difficulty = "Medium"
        self.board = None
        self.notes_mode = False

        # Timing
        self.start_time = 0
        self.elapsed_time = 0

        # Background Thread Synchronization
        self.gen_thread = None
        self.generated_data = None

        self._init_buttons()

    def _init_buttons(self):
        """Set up buttons for the menu, top bar, bottom toolbar, and win screen."""
        # Menu Difficulty Buttons
        self.menu_buttons = []
        btn_w, btn_h = 220, 56
        start_y = 290
        for i, diff in enumerate(["Easy", "Medium", "Hard"]):
            x = (WINDOW_WIDTH - btn_w) // 2
            y = start_y + i * 80
            clues = DIFFICULTIES[diff]
            label = f"{diff} ({clues} clues)"
            self.menu_buttons.append(Button(x, y, btn_w, btn_h, label, action=diff))

        # Top Bar "New Game" Button
        self.btn_top_new = Button(WINDOW_WIDTH - 140, 36, 110, 38, "New Game", action="MENU")

        # Bottom Notes Toolbar (3 buttons aligned neatly across the 540px board width)
        bar_y = BOARD_OFFSET_Y + BOARD_SIZE + 22
        b_w, b_h, gap = 170, 42, 15
        self.btn_notes_toggle = Button(BOARD_OFFSET_X, bar_y, b_w, b_h, "Notes: OFF", action="TOGGLE_NOTES")
        self.btn_auto_notes = Button(BOARD_OFFSET_X + b_w + gap, bar_y, b_w, b_h, "Auto Notes", action="AUTO_NOTES")
        self.btn_clear_notes = Button(BOARD_OFFSET_X + (b_w + gap) * 2, bar_y, b_w, b_h, "Clear Notes", action="CLEAR_NOTES")
        self.play_bottom_buttons = [
            self.btn_notes_toggle,
            self.btn_auto_notes,
            self.btn_clear_notes,
        ]

        # Win Overlay Buttons
        self.win_buttons = [
            Button(WINDOW_WIDTH // 2 - 150, 430, 135, 48, "New Game", action="MENU"),
            Button(WINDOW_WIDTH // 2 + 15, 430, 135, 48, "Quit", action="QUIT"),
        ]

    def set_notes_mode(self, enabled):
        """Set the notes mode flag and synchronize the toggle button appearance."""
        self.notes_mode = enabled
        self.btn_notes_toggle.active = enabled
        self.btn_notes_toggle.text = "Notes: ON" if enabled else "Notes: OFF"

    def start_generation(self, difficulty):
        """Spawn a daemon worker thread to generate a puzzle without freezing the UI."""
        self.difficulty = difficulty
        self.state = "GENERATING"
        self.generated_data = None
        self.set_notes_mode(False)
        clues = DIFFICULTIES[difficulty]

        def worker():
            puzzle, solution = SudokuGenerator.generate_puzzle(clues)
            self.generated_data = (puzzle, solution)

        self.gen_thread = threading.Thread(target=worker, daemon=True)
        self.gen_thread.start()

    @staticmethod
    def format_time(seconds):
        """Format elapsed seconds as mm:ss."""
        mins = int(seconds) // 60
        secs = int(seconds) % 60
        return f"{mins:02d}:{secs:02d}"


    def handle_events(self):
        mouse_pos = pygame.mouse.get_pos()

        # Update hover states
        if self.state == "MENU":
            for btn in self.menu_buttons:
                btn.update(mouse_pos)
        elif self.state == "PLAYING":
            self.btn_top_new.update(mouse_pos)
            for btn in self.play_bottom_buttons:
                btn.update(mouse_pos)
        elif self.state == "WIN":
            for btn in self.win_buttons:
                btn.update(mouse_pos)

        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                self.quit_game()

            if self.state == "MENU":
                self._handle_menu_events(event)
            elif self.state == "GENERATING":
                if event.type == pygame.KEYDOWN and event.key == pygame.K_ESCAPE:
                    self.state = "MENU"
            elif self.state == "PLAYING":
                self._handle_playing_events(event)
            elif self.state == "WIN":
                self._handle_win_events(event)

    def _handle_menu_events(self, event):
        if event.type == pygame.MOUSEBUTTONDOWN and event.button == 1:
            for btn in self.menu_buttons:
                if btn.hovered:
                    self.start_generation(btn.action)

    def _handle_playing_events(self, event):
        if event.type == pygame.MOUSEBUTTONDOWN and event.button == 1:
            if self.btn_top_new.hovered:
                self.state = "MENU"
                return

            if self.btn_notes_toggle.hovered:
                self.set_notes_mode(not self.notes_mode)
                return

            if self.btn_auto_notes.hovered:
                self.board.auto_fill_notes()
                return

            if self.btn_clear_notes.hovered:
                self.board.clear_all_notes()
                return

            # Check if click occurred inside the 9x9 board
            mx, my = event.pos
            if (BOARD_OFFSET_X <= mx < BOARD_OFFSET_X + BOARD_SIZE and
                    BOARD_OFFSET_Y <= my < BOARD_OFFSET_Y + BOARD_SIZE):
                c = (mx - BOARD_OFFSET_X) // CELL_SIZE
                r = (my - BOARD_OFFSET_Y) // CELL_SIZE
                self.board.select(r, c)

        elif event.type == pygame.KEYDOWN:
            if event.key == pygame.K_ESCAPE:
                self.state = "MENU"
            elif event.key == pygame.K_n:
                self.set_notes_mode(not self.notes_mode)
            elif event.key == pygame.K_UP:
                self.board.move_selection(-1, 0)
            elif event.key == pygame.K_DOWN:
                self.board.move_selection(1, 0)
            elif event.key == pygame.K_LEFT:
                self.board.move_selection(0, -1)
            elif event.key == pygame.K_RIGHT:
                self.board.move_selection(0, 1)
            elif event.key in (pygame.K_BACKSPACE, pygame.K_DELETE, pygame.K_0, pygame.K_KP0):
                r, c = self.board.selected
                if self.notes_mode:
                    # In Notes mode, Backspace/Delete clears all notes in the selected cell
                    if not self.board.given[r][c] and self.board.grid[r][c] == 0:
                        self.board.clear_cell_notes(r, c)
                else:
                    self.board.clear_cell()
            else:
                # Top-row 1-9 and Numpad 1-9 mapping
                num_map = {
                    pygame.K_1: 1, pygame.K_KP1: 1,
                    pygame.K_2: 2, pygame.K_KP2: 2,
                    pygame.K_3: 3, pygame.K_KP3: 3,
                    pygame.K_4: 4, pygame.K_KP4: 4,
                    pygame.K_5: 5, pygame.K_KP5: 5,
                    pygame.K_6: 6, pygame.K_KP6: 6,
                    pygame.K_7: 7, pygame.K_KP7: 7,
                    pygame.K_8: 8, pygame.K_KP8: 8,
                    pygame.K_9: 9, pygame.K_KP9: 9,
                }
                if event.key in num_map:
                    digit = num_map[event.key]
                    r, c = self.board.selected
                    if self.notes_mode:
                        self.board.toggle_note(r, c, digit)
                    else:
                        self.board.place_number(digit)
                        if self.board.check_win():
                            self.elapsed_time = time.time() - self.start_time
                            self.state = "WIN"

    def _handle_win_events(self, event):
        if event.type == pygame.KEYDOWN and event.key == pygame.K_ESCAPE:
            self.state = "MENU"
        elif event.type == pygame.MOUSEBUTTONDOWN and event.button == 1:
            for btn in self.win_buttons:
                if btn.hovered:
                    if btn.action == "MENU":
                        self.state = "MENU"
                    elif btn.action == "QUIT":
                        self.quit_game()

    def update(self):
        if self.state == "GENERATING":
            if self.generated_data is not None:
                puzzle, solution = self.generated_data
                self.board = Board(puzzle, solution)
                self.start_time = time.time()
                self.elapsed_time = 0
                self.state = "PLAYING"
        elif self.state == "PLAYING":
            self.elapsed_time = time.time() - self.start_time

    def draw(self):
        self.screen.fill(COLOR_BG)

        if self.state == "MENU":
            self._draw_menu()
        elif self.state == "GENERATING":
            self._draw_generating()
        elif self.state in ("PLAYING", "WIN"):
            self._draw_playing()
            if self.state == "WIN":
                self._draw_win_overlay()

        pygame.display.flip()

    def _draw_menu(self):
        title_surf = self.font_title.render("SUDOKU", True, COLOR_TEXT_GIVEN)
        title_rect = title_surf.get_rect(center=(WINDOW_WIDTH // 2, 150))
        self.screen.blit(title_surf, title_rect)

        sub_surf = self.font_subtitle.render("Select Difficulty", True, COLOR_TEXT_MUTED)
        sub_rect = sub_surf.get_rect(center=(WINDOW_WIDTH // 2, 210))
        self.screen.blit(sub_surf, sub_rect)

        for btn in self.menu_buttons:
            btn.draw(self.screen, self.font_btn)

    def _draw_generating(self):
        dots = "." * ((pygame.time.get_ticks() // 400) % 4)
        msg_surf = self.font_title.render(f"Generating{dots}", True, COLOR_TEXT_UI)
        msg_rect = msg_surf.get_rect(center=(WINDOW_WIDTH // 2, WINDOW_HEIGHT // 2 - 20))
        self.screen.blit(msg_surf, msg_rect)

        sub_surf = self.font_subtitle.render(
            f"Building a unique {self.difficulty} puzzle", True, COLOR_TEXT_MUTED
        )
        sub_rect = sub_surf.get_rect(center=(WINDOW_WIDTH // 2, WINDOW_HEIGHT // 2 + 35))
        self.screen.blit(sub_surf, sub_rect)

    def _draw_playing(self):
        # 1. Top Information Bar
        diff_surf = self.font_ui.render(f"Difficulty: {self.difficulty}", True, COLOR_TEXT_UI)
        self.screen.blit(diff_surf, (BOARD_OFFSET_X, 24))

        mistakes_color = COLOR_TEXT_WRONG if self.board.mistakes > 0 else COLOR_TEXT_UI
        mistakes_surf = self.font_ui.render(f"Mistakes: {self.board.mistakes}", True, mistakes_color)
        self.screen.blit(mistakes_surf, (BOARD_OFFSET_X, 58))

        score_surf = self.font_ui.render(f"Score: {self.board.score}", True, COLOR_TEXT_PLAYER)
        score_rect = score_surf.get_rect(center=(WINDOW_WIDTH // 2 - 10, 36))
        self.screen.blit(score_surf, score_rect)

        time_str = f"Time: {self.format_time(self.elapsed_time)}"
        time_surf = self.font_ui.render(time_str, True, COLOR_TEXT_UI)
        time_rect = time_surf.get_rect(center=(WINDOW_WIDTH // 2 - 10, 70))
        self.screen.blit(time_surf, time_rect)

        # Small "NOTES" indicator badge in the top bar when Notes mode is ON
        if self.notes_mode:
            badge_rect = pygame.Rect(WINDOW_WIDTH - 218, 41, 66, 28)
            pygame.draw.rect(self.screen, COLOR_BTN_ACTIVE, badge_rect, border_radius=6)
            pygame.draw.rect(self.screen, COLOR_BTN_BORDER, badge_rect, width=1, border_radius=6)
            badge_surf = self.font_badge.render("NOTES", True, COLOR_TEXT_GIVEN)
            self.screen.blit(badge_surf, badge_surf.get_rect(center=badge_rect.center))

        self.btn_top_new.draw(self.screen, self.font_ui)

        # 2. Board Panel Background
        board_rect = pygame.Rect(BOARD_OFFSET_X, BOARD_OFFSET_Y, BOARD_SIZE, BOARD_SIZE)
        pygame.draw.rect(self.screen, COLOR_PANEL, board_rect)

        # 3. Cell Highlights (Selected, Row/Col/Box, Matching Numbers)
        sel_r, sel_c = self.board.selected
        sel_val = self.board.grid[sel_r][sel_c]
        sel_box_r, sel_box_c = sel_r // 3, sel_c // 3

        for r in range(9):
            for c in range(9):
                cell_rect = pygame.Rect(
                    BOARD_OFFSET_X + c * CELL_SIZE,
                    BOARD_OFFSET_Y + r * CELL_SIZE,
                    CELL_SIZE,
                    CELL_SIZE,
                )
                val = self.board.grid[r][c]

                if (r, c) == (sel_r, sel_c):
                    pygame.draw.rect(self.screen, COLOR_SELECTED, cell_rect)
                elif sel_val != 0 and val == sel_val:
                    pygame.draw.rect(self.screen, COLOR_HIGHLIGHT_SAME, cell_rect)
                elif r == sel_r or c == sel_c or (r // 3 == sel_box_r and c // 3 == sel_box_c):
                    pygame.draw.rect(self.screen, COLOR_HIGHLIGHT_GROUP, cell_rect)

        # 4. Placed Numbers OR 3x3 Mini-Grid Notes (never both in the same cell)
        for r in range(9):
            for c in range(9):
                cell_x = BOARD_OFFSET_X + c * CELL_SIZE
                cell_y = BOARD_OFFSET_Y + r * CELL_SIZE
                val = self.board.grid[r][c]

                if val != 0:
                    if self.board.given[r][c]:
                        color = COLOR_TEXT_GIVEN
                    elif self.board.is_cell_wrong(r, c):
                        color = COLOR_TEXT_WRONG
                    else:
                        color = COLOR_TEXT_PLAYER

                    num_surf = self.font_cell.render(str(val), True, color)
                    center_x = cell_x + CELL_SIZE // 2
                    center_y = cell_y + CELL_SIZE // 2
                    num_rect = num_surf.get_rect(center=(center_x, center_y))
                    self.screen.blit(num_surf, num_rect)
                else:
                    # Render pencil marks in a 3x3 mini-grid for this empty cell
                    cell_notes = self.board.notes[r][c]
                    if cell_notes:
                        for digit in cell_notes:
                            sub_r = (digit - 1) // 3
                            sub_c = (digit - 1) % 3
                            sub_center_x = cell_x + sub_c * SUBCELL_SIZE + SUBCELL_SIZE // 2
                            sub_center_y = cell_y + sub_r * SUBCELL_SIZE + SUBCELL_SIZE // 2
                            note_surf = self.font_note.render(str(digit), True, COLOR_TEXT_NOTE)
                            note_rect = note_surf.get_rect(center=(sub_center_x, sub_center_y))
                            self.screen.blit(note_surf, note_rect)

        # 5. Grid Lines (Thin inner lines first, then thick 3x3 box boundaries)
        for i in range(1, 9):
            if i % 3 != 0:
                x = BOARD_OFFSET_X + i * CELL_SIZE
                pygame.draw.line(
                    self.screen, COLOR_GRID_THIN,
                    (x, BOARD_OFFSET_Y), (x, BOARD_OFFSET_Y + BOARD_SIZE), 1
                )
                y = BOARD_OFFSET_Y + i * CELL_SIZE
                pygame.draw.line(
                    self.screen, COLOR_GRID_THIN,
                    (BOARD_OFFSET_X, y), (BOARD_OFFSET_X + BOARD_SIZE, y), 1
                )

        for i in range(0, 10, 3):
            x = BOARD_OFFSET_X + i * CELL_SIZE
            pygame.draw.line(
                self.screen, COLOR_GRID_THICK,
                (x, BOARD_OFFSET_Y), (x, BOARD_OFFSET_Y + BOARD_SIZE), 3
            )
            y = BOARD_OFFSET_Y + i * CELL_SIZE
            pygame.draw.line(
                self.screen, COLOR_GRID_THICK,
                (BOARD_OFFSET_X, y), (BOARD_OFFSET_X + BOARD_SIZE, y), 3
            )

        # 6. Bottom Notes Toolbar Buttons
        for btn in self.play_bottom_buttons:
            btn.draw(self.screen, self.font_ui)

        # 7. Bottom Controls Hint
        hint_surf = self.font_hint.render(
            "Arrows/Click: Select  •  1-9: Fill/Note  •  N: Notes Mode  •  Del/Bksp: Clear  •  Esc: Menu",
            True, COLOR_TEXT_MUTED
        )
        hint_rect = hint_surf.get_rect(center=(WINDOW_WIDTH // 2, WINDOW_HEIGHT - 22))
        self.screen.blit(hint_surf, hint_rect)

    def _draw_win_overlay(self):
        # Semi-transparent dark backdrop
        overlay = pygame.Surface((WINDOW_WIDTH, WINDOW_HEIGHT), pygame.SRCALPHA)
        overlay.fill((20, 20, 32, 215))
        self.screen.blit(overlay, (0, 0))

        # Dialog Card
        card_rect = pygame.Rect(WINDOW_WIDTH // 2 - 220, 230, 440, 280)
        pygame.draw.rect(self.screen, COLOR_PANEL, card_rect, border_radius=14)
        pygame.draw.rect(self.screen, COLOR_BTN_BORDER, card_rect, width=2, border_radius=14)

        win_surf = self.font_title.render("You Win!", True, COLOR_TEXT_GIVEN)
        win_rect = win_surf.get_rect(center=(WINDOW_WIDTH // 2, 285))
        self.screen.blit(win_surf, win_rect)

        stats_text = (
            f"Score: {self.board.score}  •  Time: {self.format_time(self.elapsed_time)}  "
            f"•  Mistakes: {self.board.mistakes}"
        )
        stats_surf = self.font_subtitle.render(stats_text, True, COLOR_TEXT_PLAYER)
        stats_rect = stats_surf.get_rect(center=(WINDOW_WIDTH // 2, 355))
        self.screen.blit(stats_surf, stats_rect)

        for btn in self.win_buttons:
            btn.draw(self.screen, self.font_btn)

    def quit_game(self):
        pygame.quit()
        sys.exit()

    def run(self):
        while True:
            self.handle_events()
            self.update()
            self.draw()
            self.clock.tick(FPS)


if __name__ == "__main__":
    game = Game()
    game.run()