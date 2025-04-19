# Maze Generator
import pygame
import sys
import os
import re
import math
import random
import time

pygame.init()

## change constant
#! debugging
#$ current

# GLOBALS
DEBUG = False
DEFAULT_WINX = 1200 # static
DEFAULT_WINY = 900 # static
AR = DEFAULT_WINX / DEFAULT_WINY
WIN_SIZE = [DEFAULT_WINX, DEFAULT_WINY] # may change
PRESS_ESC = True
DISPLAY = pygame.display.Info()
DISPLAY_SIZE = (DISPLAY.current_w, DISPLAY.current_h) # [width,height] of hardware screen in pixels

# Path to root folder -- frozen indicates being run from binary
ROOT = '../' if getattr(sys, 'frozen', False) else './'

# Images
IMAGE_FORMAT = "jpg" # format mazes will be saved as
try:
	STAR_IMAGE = pygame.image.load(ROOT + "masks/star.png")
	CROWN_IMAGE = pygame.image.load(ROOT + "masks/crown.png")
	CROWN_2_IMAGE = pygame.image.load(ROOT + "masks/crown_2.png")
	L_ARROW = pygame.image.load(ROOT + "menu/left_arrow.png")
	R_ARROW = pygame.image.load(ROOT + "menu/right_arrow.png")
	SL_ARROW = pygame.image.load(ROOT + "menu/selected_left_arrow.png")
	SR_ARROW = pygame.image.load(ROOT + "menu/selected_right_arrow.png")
	MAZE_ICON = pygame.image.load(ROOT + "resources/maze_icon.png")
except Exception as e:
	print("Could not locate all resources...")
	print(str(e))
	sys.exit(1)

# COLORS
# ----- basic -----
WHITE = (255,255,255)
BLACK = (0,0,0)
GREY = (96,96,96)
LIGHT_GREY = (224,224,224)
RED = (255,0,0)
GREEN = (0,255,0)
BLUE = (0,0,255)
YELLOW = (255,255,0)
# --- dull ---
DIM_GREY = (60,60,60)
DIM_YELLOW = (100,100,0)
# ----- unique -----
PEACH = (255,250,205)
PEACH_2 = (230,226,184)
FORREST_GREEN = (0,153,76)
TEXT_WHITE = (230,230,230)
TEXT_YELLOW = (230,230,0)
SUCCESS_GREEN = (12,230,70)
ERROR_RED = (208,28,28)

class Block():
	def __init__(self, row, col):
		# pos in array
		self.pos = (row, col)
		# 1 = blocked
		self.left = 1
		self.right = 1
		self.top = 1
		self.bottom = 1
		# 0 = unvisited
		self.visited = 0
		return

	def borders(self):
		total = 0
		edges = [self.left, self.top, self.right, self.bottom]
		for x in edges:
			total += x
		return total

	def drawlines(self, surface, color, tilesize, line_width, frame):
		# anything drawn outside the bounds of the surface, is not seen! (the parts on screen will still be shown)
		width = tilesize
		height = tilesize
		y = (self.pos[0] - frame[0]) * tilesize
		x = (self.pos[1] - frame[1]) * tilesize
		offset = int(line_width/2)

		if self.left: # LEFT
			pos = (x-offset, y-offset)
			dim = (line_width, (height + 2*offset))
			pygame.draw.rect(surface, color, (pos, dim))
		if self.right: # RIGHT
			pos = (x-offset + width, y-offset)
			dim = (line_width, (height + 2*offset))
			pygame.draw.rect(surface, color, (pos, dim))
		if self.top: # TOP
			pos = (x-offset, y-offset)
			dim = ((width + 2*offset), line_width)
			pygame.draw.rect(surface, color, (pos, dim))
		if self.bottom: # BOTTOM
			pos = (x-offset, y-offset + height)
			dim = ((width + 2*offset), line_width)
			pygame.draw.rect(surface, color, (pos, dim))
		return

class Maze():
	## Maze specific constants
	# lengths will be relative to smallest side
	RATIO = 8/9 # (%) size of maze window relative to its full size
	MIN_TILES = 3 # cannot have a dimension smaller than this
	MAX_TILES = 50

	MIN_FRAME_SIZE = 3 # frame must show at least this many tiles per side
	MAX_FRAME_SIZE = 50 # frame cannot become larger than this (on screen)

	START_ROWS = 30 # default dimensions upon launch
	START_COLS = 20

	SCROLL_VAL = 0.5 # tiles / scroll
	SCROLL_SPEED = 5 # scrolls / sec

	START_ZOOM = 0.75 # zoom maze starts at
	ZOOM_VAL = 1 # tiles / zoom
	ZOOM_SPEED = 15 # zooms / sec

	MIN_LINE_WIDTH = 1
	MAX_LINE_WIDTH = 15
	DEFAULT_LINE_WIDTH = 3
	EXPAND_VAL = 1 # increment groups
	EXPAND_SPEED = 45 # line ticks / sec

	# largest possible maze generation
	if sys.getrecursionlimit() < (MAX_TILES ** 2):
		sys.setrecursionlimit(MAX_TILES ** 2)

	# colors
	C_BACKGROUND = PEACH_2
	C_BACKGROUND = PEACH
	C_EXITS = PEACH_2
	C_GRID = BLACK
	
	def __init__(self, dim, fps):
		self.data = [] # array of blocks
		# --- window ---
		self.surface = None
		self.win_pos = (0,0) # (x,y)
		self.width = 0
		self.height = 0
		self.fps = fps
		# --- maze ---
		self.rows = 0
		self.cols = 0
		self.tilesize = 0 # tiles are always squares
		self.start_cell = None
		self.finish_cell = None
		# --- frame ---
		self.frame_pos = [0,0] # fov [y,x] - cell at topleft of frame
		self.frame_size = (0,0) # (rows, cols)
		self.min_frame_length = Maze.MIN_FRAME_SIZE # number of tiles at largest possible zoom
		self.max_frame_length = Maze.MAX_FRAME_SIZE # number of tiles at smallest zoom (may not be able to show full maze)
		# --- scroll ---
		self.scroll_delay = int(self.fps / Maze.SCROLL_SPEED * Maze.SCROLL_VAL) # frames / scroll
		self.scroll_counter = 0
		# --- zoom ---
		self.zoom_interval = int(self.fps / Maze.ZOOM_SPEED * Maze.ZOOM_VAL) # frame / zoom
		self.zoom_delay = int(0.25 * self.fps)
		self.cont_zoom = False
		self.zoom_counter = 0
		# --- lines ---
		self.expand_interval = int(self.fps / Maze.EXPAND_SPEED * Maze.EXPAND_VAL)
		self.expand_delay = int(0.25 * self.fps)
		self.cont_expand = False
		self.expand_counter = 0
		# --- defaults ---
		self.max_screen_tiles = round(Maze.START_ZOOM * min(dim[0],dim[1])) # total number of cells that can be displayed in the window's shortest length
		self.line_width = 2 # updates
		self.adaptive_lines = True # changes based on zoom level
		self.line_color = Maze.C_GRID
		self.bg_color = Maze.C_BACKGROUND
		self.exit_color = Maze.C_EXITS
		# --- initialize ---
		self.resize(dim) # set maze and tile dimensions, fill with blank tiles
		self.update_line_size()

	def remap(self, seed=(0,0)):
		# make a new maze out of this one
		self.reset()
		self.generate(seed)
		self.find_exits()
		self.set_frame_center(self.start_cell)

	def reset(self):
		# grid of blocks (no paths)
		self.start_cell = None
		self.finish_cell = None
		self.data = []
		for y in range(self.rows):
			row = []
			for x in range(self.cols):
				block = Block(y, x)
				row.append(block)
			self.data.append(row)

	def resize(self, new_dim=None):
		# Maze: rows x columns
		if new_dim:
			self.rows = new_dim[0]
			self.cols = new_dim[1]
			self.reset() # must create data for potential new tiles (clears maze)
			self.restrict_zoom() # incase maze becomes smaller than frame (update frame from zoom in update_tilesize)
			self.update_frame_pos() # incase maze shrinks past frame location
		# adjust maze size on screen -- ratio
		# scale to make maze panel maximally fit within the program window, then adjust by a multiplier (% of max size)
		scale = min(WIN_SIZE[0] / self.cols, WIN_SIZE[1] / self.rows) * Maze.RATIO
		# Set maze window size -- keep ratio of rows to columns
		self.width = (self.cols * scale)
		self.height = (self.rows * scale)

		# Set new tile dimensions to fill the zoomed frame
		# -- readjusts window size, frame size, and window pos (position on screen)
		self.update_tilesize()

	def update_pos(self):
		# set maze window position on screen (center)
		self.surface = pygame.Surface([self.width, self.height])
		maze_x = round((WIN_SIZE[0] - self.width) / 2)
		maze_y = round((WIN_SIZE[1] - self.height) / 2)
		self.win_pos = (maze_x, maze_y)

	def update_tilesize(self):
		# set tilesize to fit the zoomed amount of tiles on screen
		# tiles are squares (width = height)

		limiting_side = min(self.width, self.height) # shorter dimension [width/height]

		# min. tile length [width or height] such that a maximum of MAX_SCREEN_TILES can be seen in the window (on the limiting side)
		current_length = limiting_side / (self.max_screen_tiles)

		# apply lower limit on tile size
		self.tilesize = current_length

		# round tilesize and adjust maze window
		self.tilesize = int(self.tilesize) # truncate to make tile bounds consistent (not offset every x tiles)

		k = (self.rows, self.cols).index(min(self.rows, self.cols)) # limiting index
		i = 0 if k else 1 # scaled index
		# ratio of longer side to smaller side --> ex. 4:3
		ratio = (self.rows, self.cols)[i] / (self.rows, self.cols)[k] # rows / cols
		maze_size = [0, 0] # [height, width]
		maze_size[k] = (self.tilesize * self.max_screen_tiles)
		maze_size[i] = (self.tilesize * self.max_screen_tiles * ratio)
		# update maze dimensions
		self.height = maze_size[0]
		self.width = maze_size[1]

		# get new frame size - (in tiles)
		frame_height = self.max_screen_tiles
		frame_width = self.max_screen_tiles
		if k == 0: # cols are larger
			frame_width = min(frame_width * ratio, self.cols) # prevent floating-point error
		else: # rows are larger
			frame_height = min(frame_height * ratio, self.rows)
		self.frame_size = (frame_height, frame_width)

		# update window position
		self.update_pos()

		if DEBUG: #!
			print("Frame size:", self.frame_size)
			print("Window size:", self.width, self.height)
			print("Tile length:", self.tilesize)
			print()

		# set line size based on zoom level
		self.update_line_size()

	def scroll(self, direction):
		if not direction[0] and not direction[1]: # do not scroll
			self.scroll_counter = 0
		# scroll
		elif self.scroll_counter <= 0:
			for i in range(2):
				self.frame_pos[i] += (direction[i] * Maze.SCROLL_VAL) # move the frame [top,left]
			self.update_frame_pos()
			self.scroll_counter = self.scroll_delay
		else: # tick
			self.scroll_counter -= 1

	def zoom(self, m):
		if m == 0: # no zoom
			self.zoom_counter = 0
			self.cont_zoom = False
		# zoom
		elif self.zoom_counter <= 0:
			# update counter
			if self.cont_zoom:
				self.zoom_counter = self.zoom_interval
			else:
				self.zoom_counter = self.zoom_delay
				self.cont_zoom = True
			# grow / shrink frame
			self.max_screen_tiles -= (m * Maze.ZOOM_VAL)
			# restrict bounds -- so that the screen cannot be zoomed out more than necessary, or in more than desired
			self.restrict_zoom()
			target = self.mouse_cell() # save mouse cell before zoom
			self.resize() # set new maze dimensions
			# anchor the frame closest to where the mouse is
			self.set_frame_to_cursor(target)
			self.update_frame_pos() # fix bounds
		else: # tick
			self.zoom_counter -= 1

	def restrict_zoom(self):
		# cannot zoom in past predefined minimum
		# cannot display more tiles that exist
		if self.max_screen_tiles < self.min_frame_length: # lower cap
			self.max_screen_tiles = self.min_frame_length
		elif self.max_screen_tiles > min(self.rows, self.cols): # all tiles shown
			self.max_screen_tiles = min(self.rows, self.cols)
		elif self.max_screen_tiles > self.max_frame_length: # upper cap
			self.max_screen_tiles = self.max_frame_length

	def get_zoom(self, screen_tiles=None):
		# use current maze settings
		if not screen_tiles:
			screen_tiles = self.max_screen_tiles
		# percent of total tiles shown
		return round(self.max_screen_tiles / min(self.rows, self.cols), 2)

	def set_zoom(self, zoom, align=True):
		# zoom should be between 0 to 1.00 (percent as decimal)
		if zoom < 0:
			zoom = 0
		elif zoom > 1:
			zoom = 1
		self.max_screen_tiles = zoom * min(self.rows, self.cols)
		if align: # must be a whole amount of tiles
			self.max_screen_tiles = round(self.max_screen_tiles)
		self.restrict_zoom()
		self.resize() # set new dimensions
		self.update_frame_pos() # restrict bounds

	def get_line_size(self, screen_tiles=None):
		# use current maze settings
		if not screen_tiles:
			screen_tiles = max(self.frame_size)
		# calculate an appropriate line size based on visible tiles
		line_size = 0
		if screen_tiles <= 3:
			line_size = 15
		elif screen_tiles <= 5:
			line_size = 9
		elif screen_tiles <= 7:
			line_size = 5
		elif screen_tiles <= 10:
			line_size = 3
		elif screen_tiles <= 15:
			line_size = 2
		else:
			line_size = 1
		return line_size

	def update_line_size(self):
		# update line size - should be called when max screen tiles changes (for adaptive size)
		if self.adaptive_lines:
			self.line_width = self.get_line_size() # based on zoom

	def expand_lines(self, w):
		if self.adaptive_lines: # can not override automatic line width
			return
		if w == 0: # no expansion
			self.expand_counter = 0
			self.cont_expand = False
		# expand lines
		elif self.expand_counter <= 0:
			# update counter
			if self.cont_expand:
				self.expand_counter = self.expand_interval
			else:
				self.expand_counter = self.expand_delay
				self.cont_expand = True
			# grow / shrink frame
			self.line_width += int(w * self.EXPAND_VAL)
			# fix bounds
			if self.line_width > self.MAX_LINE_WIDTH:
				self.line_width = self.MAX_LINE_WIDTH
			elif self.line_width < self.MIN_LINE_WIDTH:
				self.line_width = self.MIN_LINE_WIDTH
		else: # tick
			self.expand_counter -= 1

	def toggle_adaptive_lines(self):
		if self.adaptive_lines:
			self.adaptive_lines = False
		else:
			self.adaptive_lines = True

	def update_frame_pos(self):
		# restrict bounds of frame to bounds of maze
		for i in range(2):
			if self.frame_pos[i] < 0: # top/left [negative]
				self.frame_pos[i] = 0
			elif self.frame_pos[i] + self.frame_size[i] > [self.rows, self.cols][i]: # bottom/right [positive]
				self.frame_pos[i] = [self.rows, self.cols][i] - self.frame_size[i]

	def align_frame(self):
		# only align if positive or negative side of frame is on a partial tile
		aligned = True
		# check bottom / right
		for i in range(2):
			if (self.frame_pos[i] + self.frame_size[i]) - int(self.frame_pos[i] + self.frame_size[i]) != 0:
				aligned = False

		if aligned:
			return
		# else it will be aligned to top of frame (nothing will happen if its top aligned already)
				
		# center frame on nearest cell
		for i in range(2):
			self.frame_pos[i] = round(self.frame_pos[i])
		self.update_frame_pos() # prevent aligning past maze bounds

	def set_frame_quadrant(self, quadrant):
		if quadrant < 1 or quadrant > 4:
			quadrant = 3 # default

		if quadrant == 1 or quadrant == 2:
			self.frame_pos[0] = 0 # anchor top
		else:
			self.frame_pos[0] = self.rows - self.frame_size[0] # anchor bottom

		if quadrant == 2 or quadrant == 3:
			self.frame_pos[1] = 0 # anchor left
		else:
			self.frame_pos[1] = self.cols - self.frame_size[1] # anchor right

	def set_frame_center(self, cell):
		# center frame around chosen cell
		y = cell[0] - self.frame_size[0]/2 + 0.5
		x = cell[1] - self.frame_size[1]/2 + 0.5
		self.frame_pos[0] = y
		self.frame_pos[1] = x
		self.update_frame_pos() # check bounds

	def set_frame_to_cursor(self, cell):
		pos = self.get_cursor() # [x,y]
		if pos and cell:
			pos.reverse() # [y,x]
			# move frame to center of target cell -- moves top-left corner of frame
			for i in range(2):
				k = 1 if i == 0 else 0 # opposite index
				# row, then col
				self.frame_pos[i] = cell[i]
				# now move frame back, so that the target is at the mouse location
				self.frame_pos[i] -= pos[i] / self.tilesize # frame is in units of tiles
			
	def get_cursor(self):
		# find mouse coordinates relative to maze window
		cursor = pygame.mouse.get_pos() # [x,y]
		pos = [c - o for (c,o) in zip(cursor, self.win_pos)] # translate so that win_pos is the origin
		# check if cursor is on maze
		for i in range(2):
			if pos[i] < 0 or pos[i] >= [self.width,self.height][i]:
				pos = None # outside maze
				break
		return pos

	def mouse_cell(self):
		# find which cell the mouse is in
		cursor_pos = self.get_cursor()
		if not cursor_pos:
			return None # does not exist
		# flip -- y, x
		cursor_pos.reverse()
		cell_pos = [-1,-1]
		# convert from [x,y] to cell coordinates
		for i in range(2):
			k = 1 if i == 0 else 0 # opposite index
			cell_pos[i] = cursor_pos[i] / self.tilesize + self.frame_pos[i] # fraction
		return cell_pos

	def random_location(self):
		row = random.randint(0, (self.rows - 1))
		col = random.randint(0, (self.cols - 1))
		return (row,col)

	def unblock(self, pos1, pos2):
		# create a path from pos1 to pos2
		row1 = pos1[0]
		row2 = pos2[0]
		col1 = pos1[1]
		col2 = pos2[1]
		# From pos2 to pos1
		y = int(pos2[0] - pos1[0])
		x = int(pos2[1] - pos1[1])
		# Errors
		if abs(x) > 1 or abs(y) > 1:
			return -1 # not adjacent cells
		elif x == 0 and y == 0:
			return -2 # same cell
		elif abs(x) == 1 and abs(y) == 1:
			return -3 # diagonal cell
		# Remove the Barrier (relative to pos1 cell)
		if x == -1: # LEFT
			self.data[row1][col1].left = 0
			self.data[row2][col2].right = 0
		elif x == 1: # RIGHT
			self.data[row1][col1].right = 0
			self.data[row2][col2].left = 0
		elif y == -1: # TOP
			self.data[row1][col1].top = 0
			self.data[row2][col2].bottom = 0
		elif y == 1: # BOTTOM
			self.data[row1][col1].bottom = 0
			self.data[row2][col2].top = 0

	def find_neighbours(self, cell, blocks):
		# returns a list of pos of neighbour cells
		# adds unvisited, reachable neighbours to blocks
		row = cell[0]
		col = cell[1]
		neighbours = [[row,col-1], [row-1,col], [row,col+1], [row+1,col]] # adjacent cells
		for p in neighbours.copy(): # only removes neighbours from the original list, not the iterable
			y = p[0]
			x = p[1]
			# remove out-of-bounds
			if x < 0 or x >= self.cols: # col
				neighbours.remove(p)
			elif y < 0 or y >= self.rows: # row
				neighbours.remove(p)
			else:
				new_block = self.data[y][x] # exists
				if new_block.visited: # visited
					neighbours.remove(p)
				else: # unvisited
					blocks.append(new_block) # add block
		return neighbours

	def check_visited(self):
		total = 0
		for row in range(len(self.data)):
			for col in range(len(self.data[row])):
				block = self.data[row][col]
				if block.visited:
					total += 1
		return total

	def generate(self, cell):
		# index of cell - [row, col]
		row = cell[0]
		col = cell[1]
		curr_block = self.data[row][col]
		curr_block.visited = 1

		unvisited_blocks = [] # cells that can be visited
		neighbours = self.find_neighbours(cell, unvisited_blocks) # positions of unvisited cells

		while neighbours:
			# choose random cell to advance to
			i = random.randint(1, len(neighbours)) - 1
			next_block = unvisited_blocks[i]
			# remove the barrier
			pos2 = [neighbours[i][0], neighbours[i][1]]
			err = self.unblock(cell, pos2)
			if err:
				if err == -1:
					print('Error unblock() - non-adjacent cells')
				elif err == -2:
					print('Error unblock() - same cell')
				elif err == -3:
					print('Error unblock() - diagonal cell')
			# recurse with the new cell
			self.generate(pos2)
			# update visited neighbours when returned back to this cell
			unvisited_blocks = []
			neighbours = self.find_neighbours(cell, unvisited_blocks)
			if len(unvisited_blocks) != len(neighbours):
				print('Error generate() - # of neighbours does not match unvisited blocks')
				break
		else:
			# retreat back to an old cell
			return

	def find_cell(self, cell, n, radius=0, cw=1, dir=[]): # closest block from the cell that has n borders
		if DEBUG:
			print('Find a cell with (%d) borders from [%d,%d] - r=%d' % (n, cell[0], cell[1], radius)) #!
		# chosen cell
		center_row = cell[0]
		center_col = cell[1]
		# Ring
		# define bounds
		top = center_row - radius
		bottom = center_row + radius
		left = center_col - radius
		right = center_col + radius
		# choose starting cell -- dir [x,y]
		if not dir:
			dir = [-1,-1] # default
		# ROW
		if dir[1] == 0:
			y = center_row
		elif dir[1] == 1:
			y = bottom
		else: # default
			y = top
		# COL
		if dir[0] == 0:
			x = center_col
		elif dir[0] == 1:
			x = right
		else: # default
			x = left
		# chose center
		if y == x:
			y = top # override

		# Initialize starting point
		pos = [y,x]
		start_pos = None
		set_start = False

		# Set initial direction
		# increments row or column
		if dir[0] == 0: # col=0
			i = 1 # inc. col
		elif dir[1] == 0: # row=0
			i = 0 # inc. row
		elif dir[0] == dir[1]: # top-left, bottom-right
			if cw == 1:
				i = 1 # inc. col
			else: # ccw
				i = 0 # inc. row
		else: # bottom-left, top-right
			if cw == 1:
				i = 1 # inc. row
			else: # ccw
				i = 0 # inc. col

		# Search in the ring
		# ===================
		while True:
			# Check cell exists on map
			for _ in range (2):
				if pos[0] < 0: # ABOVE map
					pos[0] = 0 # row=top
					# col is left/right
					if cw == 1:
						pos[1] = right
					else:
						pos[1] = left
					i = 0 # move vertically
				elif pos[0] >= self.rows: # BELOW map:
					pos[0] = self.rows-1 # row=bottom
					# col is left/right
					if cw == 1:
						pos[1] = left
					else:
						pos[1] = right
					i = 0 # move vertically
				elif pos[1] < 0: # LEFT of map
					pos[1] = 0 # col=left
					# row is top/bottom
					if cw == 1:
						pos[0] = top
					else:
						pos[0] = bottom
					i = 1 # move horizontally
				elif pos[1] >= self.cols: # RIGHT of map
					pos[1] = self.cols-1 # col=right
					# row is top/bottom
					if cw == 1:
						pos[0] = bottom
					else:
						pos[0] = top
					i = 1 # move horizontally

			# Define start pos
			if not set_start:
				start_pos = pos.copy() # COPY (not linked to the current position)
				set_start = True
				if DEBUG:
					print(pos) #! start pos
					print('*****')
			# Check if completed ring
			else:
				if pos == start_pos: # completed loop
					if DEBUG:
						print('Finished cycle %d\n' % radius) #!
					break
				if DEBUG:
					print(pos) #! current pos
					print('-----') 

			# Inspect cell
			block = self.data[pos[0]][pos[1]]
			if block.borders() == n:
				if DEBUG:
					print('Found Cell!\n') #!
				return block # FOUND CELL

			# Move to the next cell
			if left == right: # 0 radius case
				continue
			if i == 0: # moving vertically
				if pos[1] == right: # positive
					pos[i] += cw
				elif pos[1] == left: # reversed
					pos[i] -= cw
				else:
					print('Error find_cell() - moving vertically [wrong column]')
			elif i == 1: # moving horizontally
				if pos[0] == top: # positive
					pos[i] += cw
				elif pos[0] == bottom: # reversed
					pos[i] -= cw
				else:
					print('Error find_cell() - moving horizontally [wrong row]')
			else:
				print('Error find_cell - index not defined')
			# Update direction (at corners)
			if pos in [[top,left], [top,right], [bottom,left], [bottom,right]]: # corner
				i = abs(i-1) # flip col/row

		# Could not find a match in the ring!
		if radius >= (max(self.rows,self.cols)-1): # could not find any matching cell
			print('Error find_cell() - no cell has %d borders!' % n)
			return -1
		else:
			return self.find_cell(cell, n, radius=(radius+1), cw=cw, dir=dir) # SEARCH AGAIN, +1 radius

	def check_valid(self):
		valid = True
		for row in range(len(self.data)):
			for col in range(len(self.data[row])):
				if self.data[row][col].borders() == 4:
					valid = False
					break
		return valid

	def check_cell(self, cell):
		block = self.data[cell[0]][cell[1]]
		print('Left: ' + str(block.left))
		print('Right: ' + str(block.right))
		print('Top: ' + str(block.top))
		print('Bottom: ' + str(block.bottom))
		print()

	def draw_borders(self):
		upper_bounds = [0,0] # [first_row, first_col] -- top and left
		lower_bounds = [0,0] # [last_row, last_col] -- bottom and right
		# set bounds -- frame_size[i] rows/cols fit on window except when half of a row/col is drawn, then frame_size[i]+1 rows/cols are on screen (two 'half' tiles on either end)
		for i in range(2):
			upper_bounds[i] = int(self.frame_pos[i]) # round down so the 'half' tile is drawn at one of the upper bounds
		for i in range(2):
			# frame_size is a constant
			lower_bounds[i] += math.ceil(self.frame_pos[i] + self.frame_size[i]) # round up so the 'half' tile is drawn at one of the lower bounds

		# Draw All
		for row in range(upper_bounds[0], lower_bounds[0]): # remember loop does not count last index (so -1 is not added)
			for col in range(upper_bounds[1], lower_bounds[1]):
				new_block = self.data[row][col]
				new_block.drawlines(self.surface, self.line_color, self.tilesize, self.line_width, self.frame_pos)
		return

	def draw_star(self, cell, color, size=100, points=5, incline=0.55, start_angle=(math.pi/2)):
		# draw a star at cell [y,x]
		if size < 0 or size > 100:
			size = 100
		# pos relative to frame
		pos = [point - frame for (point,frame) in zip(self.data[cell[0]][cell[1]].pos, self.frame_pos)]
		for i in range(2): # check if in frame
			if pos[i]+1 <= 0 or pos[i] >= self.frame_size[i]:
				return 1 # cannot draw to this cell
		width = self.tilesize * (size/100) # percent visible
		height = self.tilesize * (size/100)
		x = pos[1]*self.tilesize + (self.tilesize - width) / 2
		y = pos[0]*self.tilesize + (self.tilesize - height) / 2
		rect = [x, y, width, height]
		coordinates = self.create_star(rect, points, incline, start_angle) # star vertices in order
		pygame.draw.polygon(self.surface, color, coordinates)
		
	def create_star(self, rect, points=5, incline=0.45, start_angle=(math.pi / 2)):
		# star must have at least 4 points
		if points < 4:
			points = 4
		# incline is how steep the points are
		if incline < 0 or incline > 1:
			incline = 0.55 # default
		x, y, width, height = rect
		outer_radius = min(width, height) / 2
		inner_radius = incline * outer_radius
		point_list = []
		arc_length = (2 * math.pi) / (2 * points)

		# remember quadrants are flipped vertically because pos grow going down (+pi)
		points = int(points) # safety
		for i in range(2*points):
			if i % 2 == 0: # even
				r = outer_radius
			else: # odd
				r = inner_radius
			a = (i * arc_length) + start_angle + math.pi # current angle
			p = [math.cos(a) * r, math.sin(a) * r]
			point_list.append(p)

		# translate to rect location
		center = [x + width/2, y + height/2]
		for i in range(2*points):
			for k in range(2):
				point_list[i][k] += center[k]
		return point_list

	def paint(self, cell, color, size=100, symbol=None): 
		# fill a cell [y,x] with a color
		if size < 0 or size > 100:
			size = 100
		# pos relative to frame
		pos = [point - frame for (point,frame) in zip(cell, self.frame_pos)]
		for i in range(2): # check if in frame
			if pos[i]+1 <= 0 or pos[i] >= self.frame_size[i]:
				return 1 # cannot paint cell
		width = (self.tilesize * (size/100)) # percent visible
		height = (self.tilesize * (size/100))

		# color cell
		if symbol == None: # square
			x = pos[1]*self.tilesize + (self.tilesize - width) / 2
			y = pos[0]*self.tilesize + (self.tilesize - height) / 2
			rect = (x, y, width, height)
			pygame.draw.rect(self.surface, color, rect)
		else:
			design = symbol.copy().convert_alpha() # surface
			# multiplier to maximally fit design into a tile (limited by the smallest scaled side that will fit in the rect)
			scale = min(width / design.get_width(), height / design.get_height())
			design_width = design.get_width() * scale
			design_height = design.get_height() * scale
			design = pygame.transform.scale(design, (design_width, design_height))
			# center the resized design
			design_x = pos[1]*self.tilesize + (self.tilesize - design_width) / 2
			design_y = pos[0]*self.tilesize + (self.tilesize - design_height) / 2
			design_rect = (design_x, design_y, design_width, design_height)
			# color the design -- black will be transparent, white will be overridden with color
			design.set_colorkey(BLACK)
			design.fill(color, special_flags=pygame.BLEND_MIN) # keeps lower rgb value (fill or previous)
			# draw design
			self.surface.blit(design, design_rect)
		return 0

	def find_exits(self):
		# Choose start and finish zones
		start_seed = [self.rows-1, 0] # bottom left
		finish_seed = [0, self.cols-1] # top right
		self.start_cell = self.find_cell(start_seed, 3).pos
		self.finish_cell = self.find_cell(finish_seed, 3, cw=-1).pos

	def draw_exits(self):
		# Draw start / finish
		self.paint(self.start_cell, self.exit_color)
		self.paint(self.finish_cell, self.exit_color)

	def fill(self):
		self.surface.fill(self.bg_color)

	def draw(self):
		self.fill()
		self.draw_exits()
		self.draw_borders()

	def draw_board(self, outer_surface, border_size=None, color=None):
		if border_size == None:
			border_size = int(self.line_width/2) ## default
		if color == None:
			color = self.line_color
		
		# create board
		board_width = self.width + (border_size * 2)
		board_height = self.height + (border_size * 2)
		# when on bottom or right maze edge, add 1 pixel to that side's border (adjusts for maze line imblanace)
		if self.frame_pos[0] + self.frame_size[0] == self.rows:
			board_height += 1
		if self.frame_pos[1] + self.frame_size[1] == self.cols:
			board_width += 1
		board_surface = pygame.Surface((board_width, board_height))
		board_surface.fill(color)

		# position
		board_x = self.win_pos[0] - border_size
		board_y = self.win_pos[1] - border_size
		
		# place
		outer_surface.blit(board_surface, (board_x, board_y))

	def paint_paper(self, paper, cell, tilesize, color, size=100, symbol=None):
		# fill size
		width = tilesize * (size/100) # percent visible
		height = tilesize * (size/100)

		# fill with color
		if symbol == None: # square
			x = cell[1] * tilesize + (tilesize - width) / 2
			y = cell[0] * tilesize + (tilesize - height) / 2
			rect = (x, y, width, height)
			pygame.draw.rect(paper, color, rect)
		else: # fill with design
			design = symbol.copy().convert_alpha() # surface
			# maximally fit design into the tile
			scale = min(width/design.get_width(), height/design.get_height())
			design_width = design.get_width() * scale
			design_height = design.get_height() * scale
			design = pygame.transform.scale(design, (design_width, design_height))
			# center the resized design
			design_x = cell[1] * tilesize + (tilesize - design_width) / 2
			design_y = cell[0] * tilesize + (tilesize - design_height) / 2
			design_rect = (design_x, design_y, design_width, design_height)
			# color the design -- black will be transparent, white will be overridden with color
			design.set_colorkey(BLACK)
			design.fill(color, special_flags=pygame.BLEND_MIN) # keeps lower rgb value (fill or previous)
			# draw design
			paper.blit(design, design_rect)
		return

	def to_paper(self, colored, frame_width=None, frame_color=None, p_margin=0, tilesize=50):
		# tilesize only affects the length of tiles used to render the maze,
		# the canvas can always be resized.
		# draw full maze on a new canvas
		if self.adaptive_lines:
			line_width = self.get_line_size(max(self.rows, self.cols))
		else:
			line_width = self.line_width # current line width
		# default choices
		if frame_width == None:
			frame_width = int(line_width/2) # on either side
		if frame_color == None:
			frame_color = self.line_color

		maze_width = (tilesize * self.cols)
		maze_height = (tilesize * self.rows)
		maze_pos = (frame_width, frame_width) # on board
		maze_layer = pygame.Surface((maze_width, maze_height)) # inner surface

		# add one to negative borders to balance frame
		board_width = maze_width + (frame_width * 2) + 1
		board_height = maze_height + (frame_width * 2) + 1
		maze_board = pygame.Surface((board_width, board_height))

		# normal color
		line_color = self.line_color
		bg_color = self.bg_color
		exit_color = self.exit_color
		margin_color = WHITE
		# make black and white
		if not colored:
			line_color = BLACK
			frame_color = BLACK
			bg_color = WHITE
			exit_color = LIGHT_GREY

		# draw maze
		maze_layer.fill(bg_color) # background

		# exits
		self.paint_paper(maze_layer, self.start_cell, tilesize, exit_color)
		self.paint_paper(maze_layer, self.finish_cell, tilesize, exit_color)

		# lines
		for row in range(self.rows):
			for col in range(self.cols):
				# no frame, since we are drawing the entire maze
				new_block = self.data[row][col]
				new_block.drawlines(maze_layer, line_color, tilesize, line_width, (0,0))

		# borders - closed around all edges (no frame)
		maze_board.fill(frame_color)

		# paste maze to board
		maze_board.blit(maze_layer, maze_pos)
		if not p_margin: # no page margins - the board layer is the whole canvas
			return maze_board

		# get width of margin (for all sides)
		margin_width = int(min(board_width, board_height) * (p_margin/100) / 2)
		board_pos = (margin_width, margin_width) # on canvas

		# add page margins
		canvas_width = board_width + (margin_width * 2)
		canvas_height = board_height + (margin_width * 2)
		canvas = pygame.Surface((canvas_width, canvas_height))
		canvas.fill(margin_color)

		# add maze to canvas
		canvas.blit(maze_board, board_pos)
		return canvas

	def save_image(self, filepath, colored, frame_width=None, frame_color=None, size=None, bound=0):
		# size - the maximum / minimum length that the image surface may be
		# bound - 0 = minimum length, 1 = maximum length

		# create full maze
		image_surface = self.to_paper(colored, frame_width, frame_color)

		# find image size
		if size:
			if bound == 0: # minimum
				scale = size / min(self.width, self.height)
			else: # maximum
				scale = size / max(self.width, self.height)
			# set dimensions
			image_width = scale * self.width
			image_height = scale * self.height
			# scale
			pygame.transform.scale(image_surface, (image_width, image_height))

		# save as file
		pygame.image.save(image_surface, filepath)
		

class Player():
	## Player specific constants
	MIN_SPEED = 1
	MAX_SPEED = 30
	DEFAULT_SPEED_1 = 6
	DEFAULT_SPEED_2 = 18
	MIN_MOVE_DELAY = 0.25
	MIN_SIZE = 5
	MAX_SIZE = 100
	DEFAULT_SIZE = 70
	GROWTH_SPEED = 15 # growth ticks per sec
	GROWTH_UNIT = 5 # increase size in groups
	DIR_PRIORITY = 1
	MANUAL_OVERRIDE = True # tap to move instantly
	COLOR = FORREST_GREEN
	def __init__(self, color, fps):
		self.fps = fps
		self.cell = [0,0] # [y,x]
		self.color = color
		self.set_highlight() # self.highlight
		self.escaped = False
		self.victory_symbol = 0
		# size
		self.size = Player.DEFAULT_SIZE # percent of tile
		self.grow_interval = round(self.fps / Player.GROWTH_SPEED)
		self.grow_delay = 0.5 * self.fps
		self.cont_grow = False
		self.grow_counter = 0
		# movement
		self.dir_priority = 1 # 0 = horizontally, 1 = vertically
		self.manual_override = True # tap to move instantly
		self.ms_1 = Player.DEFAULT_SPEED_1 # movement speed options
		self.ms_2 = Player.DEFAULT_SPEED_2
		self.alt_speed = False # using ms 2
		self.set_speed(fps, self.ms_1)
		self.cont_movement = False
		self.move_counter = 0

	def set_speed(self, fps, speed):
		# bounds
		if speed > Player.MAX_SPEED:
			speed = Player.MAX_SPEED
		elif speed < Player.MIN_SPEED:
			speed = Player.MIN_SPEED
		self.fps = fps
		self.speed = speed # moved tiles / second
		self.move_interval = round(self.fps / self.speed) # frames / tile moved
		self.move_delay = int(Player.MIN_MOVE_DELAY * fps) # frames until moving becomes continuous
		if self.move_delay < self.move_interval:
			self.move_delay = self.move_interval

	def update_speed(self):
		# refresh movement properties with newly set speed
		# apply new speed from same mode
		if self.alt_speed:
			self.set_speed(self.fps, self.ms_2)
		else:
			self.set_speed(self.fps, self.ms_1)

	def set_pos(self, new_cell):
		self.cell = list(new_cell)
	
	def grow(self, direction):
		if direction == 0: # do not grow
			self.grow_counter = 0
			self.cont_grow = False
		# grow
		elif self.grow_counter <= 0:
			if self.cont_grow:
				self.grow_counter = self.grow_interval
			else:
				self.grow_counter = self.grow_delay
				self.cont_grow = True
			self.size += (direction * Player.GROWTH_UNIT)
			self.update_size()
		else: # tick counter
			self.grow_counter -= 1

	def update_size(self, new_size=None):
		if new_size != None:
			self.size = new_size
		if self.size > Player.MAX_SIZE: # bounds
			self.size = Player.MAX_SIZE
		elif self.size < Player.MIN_SIZE:
			self.size = Player.MIN_SIZE

	def check_escaped(self, exit_cell):
		if self.cell[0] == exit_cell[0] and self.cell[1] == exit_cell[1]:
			if not self.escaped: # one-time activation
				self.escaped = True
				self.choose_victory_symbol()

	def choose_victory_symbol(self):
		chance = random.randint(1,100)
		if chance <= 40:
			self.victory_symbol = 0 # star
		elif chance <= 80:
			self.victory_symbol = 1 # crown
		elif chance <= 100:
			self.victory_symbol = 2 # hidden crown

	def set_highlight(self, color=None):
		if not color:
			self.highlight = create_contrast(self.color, difference=25, darken_threshold=75)
		else:
			self.highlight = color

	def advance_vertically(self, dir, data):
		# UP
		if dir[0] < 0:
			if data[self.cell[0]][self.cell[1]].top == 0: # free top
				self.cell[0] += dir[0]
				return True
		# DOWN
		if dir[0] > 0:
			if data[self.cell[0]][self.cell[1]].bottom == 0: # free bottom
				self.cell[0] += dir[0]
				return True
		return False # did not move

	def advance_horizontally(self, dir, data):
		# LEFT
		if dir[1] < 0:
			if data[self.cell[0]][self.cell[1]].left == 0: # free left
				self.cell[1] += dir[1]
				return True
		# RIGHT
		if dir[1] > 0:
			if data[self.cell[0]][self.cell[1]].right == 0: # free right
				self.cell[1] += dir[1]
				return True
		return False # did not move

	def move(self, dir, data):
		# only advance in one direction per move
		# only add movement delay if player successfully moved

		# can move
		if self.move_counter <= 0:
			move_functions = [self.advance_horizontally, self.advance_vertically]
			# 1 = vertical movement takes precedence
			# 0 = horizontal movement takes precedence
			direction = 1 if self.dir_priority else 0
			alt_direction = 0 if self.dir_priority else 1
			# try to move
			moved = move_functions[direction](dir, data)
			# try other direction
			if not moved:
				moved = move_functions[alt_direction](dir, data)
			# add delay
			if moved:
				# constant rate
				if self.cont_movement:
					self.move_counter = self.move_interval
				else: # initial delay
					self.cont_movement = True
					self.move_counter = self.move_delay
		else:
			self.move_counter -= 1 # another frame passed

	def draw(self, maze):
		maze.paint(self.cell, self.color, self.size)
		# draw design
		if self.escaped:
			design_size = int(0.75 * self.size)
			# star
			if self.victory_symbol == 0:
				maze.draw_star(self.cell, self.highlight, size=design_size, incline=0.45)
			# crown
			elif self.victory_symbol == 1:
				maze.paint(self.cell, self.highlight, size=design_size, symbol=CROWN_IMAGE)
			# hidden crown
			elif self.victory_symbol == 2:
				maze.paint(self.cell, self.highlight, size=design_size, symbol=CROWN_2_IMAGE)

class Text():
	def __init__(self, text, font, fc, bc=None):
		self.font = font
		self.fg_color = fc
		self.bg_color = bc
		self.text = text
		self.surface = None
		self.rect = None
		self.update()
	def get_width(self):
		return self.rect.width
	def get_height(self):
		return self.rect.height
	def update(self, resize=True): # change text or color manually
		self.surface = self.font.render(self.text, True, self.fg_color, self.bg_color)
		if resize:
			self.rect = self.surface.get_rect()
	def draw(self, canvas):
		# manually move the rect to desired pos
		canvas.blit(self.surface, self.rect)

class MultiText(): # to control different parts of the same text
	def __init__(self, text, font, fcs, bcs=None):
		self.font = font
		self.text = text
		self.segments = len(self.text)
		if isinstance(fcs, tuple):
			self.fc_list = [fcs] * self.segments
		else:
			self.fc_list = fcs
		if not bcs:
			self.bc_list = [None] * self.segments
		else:
			self.bc_list = bcs
		self.surfaces = [None] * self.segments
		self.rects = [None] * self.segments
		self.update()
	def get_width(self):
		width = 0
		for r in self.rects:
			width += r.width
		return width
	def get_height(self):
		return self.rect.height
	def append_text(self, new_segment, fc, bc): # removes oldest segment
		self.text.pop(0)
		self.text.append(new_segment)
		self.fc_list.pop(0)
		self.fc_list.append(fc)
		self.bc_list.pop(0)
		self.bc_list.append(bc)
	def color_all(self, fc, bc=None):
		for i in range(self.segments):
			self.fc_list[i] = fc
			self.bc_list[i] = bc
	def align_text(self):
		# move all text pieces to be in line with the first rect
		for i in range(1, self.segments):
			x = self.rects[i-1].right
			y = self.rects[i-1].top
			self.rects[i].topleft = (x,y)
		return
	def update(self, resize=True):
		for i in range(self.segments):
			self.surfaces[i] = self.font.render(self.text[i], True, self.fc_list[i], self.bc_list[i])
			if resize:
				self.rects[i] = self.surfaces[i].get_rect()
		if resize:
			self.align_text() # put segments end-to-end
	def draw(self, canvas):
		for i in range(self.segments):
			canvas.blit(self.surfaces[i], self.rects[i])

class Background():
	## Background specific constants
	DAY_COLOR = PEACH_2
	NIGHT_COLOR = BLACK
	MAX_BORDER_SIZE = 50
	MIN_BORDER_SIZE = 0
	DEFAULT_BORDER = 2
	INCR_SPEED = 30 # ticks per sec
	BORDER_INCR = 1 # increment in groups of
	STEP_SIZE = 5 # larger groups
	def __init__(self, fps, day=None, night=None):
		if not day:
			day = Background.DAY_COLOR
		if not night:
			night = Background.NIGHT_COLOR
		self.day_color = day
		self.night_color = night
		self.selector = 0 # 0 - day, 1 - night
		# frame borders
		self.border_size = Background.DEFAULT_BORDER
		self.resize_interval = round(fps / Background.INCR_SPEED)
		self.resize_delay = int(0.25 * fps)
		self.cont_resize = False
		self.resize_counter = 0
		self.adaptive_frame = False # changes based on active background
		# colors
		self.color = None
		self.frame_color = None
		self.choose()
	def toggle(self):
		self.selector = 0 if self.selector else 1
		self.choose()
	def choose(self):
		self.color = [self.day_color, self.night_color][self.selector]
		self.color_frame()
	def color_frame(self, color=None):
		# ignores color if adaptive, otherwise sets the new color (if not null)
		if self.adaptive_frame:
			self.frame_color = create_contrast(self.color, difference=25, darken_threshold=30)
		elif color:
			self.frame_color = color
	def toggle_adaptive_frame(self):
		if self.adaptive_frame:
			self.adaptive_frame = False
		else:
			self.adaptive_frame = True
	def resize_frame(self, r=0):
		if r == 0: # do not increase
			self.resize_counter = 0 # can resize again immediately
			self.cont_resize = False
		# resize
		elif self.resize_counter > 0:
			self.resize_counter -= 1
		else:
			# delay
			if self.cont_resize:
				self.resize_counter = self.resize_interval
			else:
				self.resize_counter = self.resize_delay
				self.cont_resize = True
			# update borders
			self.border_size += (r * Background.BORDER_INCR)
			# bounds
			if self.border_size > Background.MAX_BORDER_SIZE:
				self.border_size = Background.MAX_BORDER_SIZE
			elif self.border_size < Background.MIN_BORDER_SIZE:
				self.border_size = Background.MIN_BORDER_SIZE

# FUNCTIONS
# --- screen ---
def screen_init(): # adjust the window size to fit on display screen
	global WIN_SIZE
	global DEFAULT_WINX
	global DEFAULT_WINY
	global AR
	for i in range(2):
		if WIN_SIZE[i] > DISPLAY_SIZE[i]:
			k = 1 if i == 0 else 0
			r = DISPLAY_SIZE[i] / WIN_SIZE[i] # ratio to fit on screen
			WIN_SIZE[i] = int(WIN_SIZE[i] * r)
			WIN_SIZE[k] = int(WIN_SIZE[k] * r)
	# new defaults (can fit on display)
	DEFAULT_WINX = WIN_SIZE[0]
	DEFAULT_WINY = WIN_SIZE[1]
	AR = DEFAULT_WINX / DEFAULT_WINY

def enter_fullscreen():
	global WIN_SIZE
	for i in range(2):
		WIN_SIZE[i] = DISPLAY_SIZE[i]
	new_screen = pygame.display.set_mode(WIN_SIZE, flags=pygame.FULLSCREEN)
	return new_screen

def exit_fullscreen():
	global WIN_SIZE
	WIN_SIZE = [DEFAULT_WINX,DEFAULT_WINY] # restore defaults
	new_screen = pygame.display.set_mode(WIN_SIZE)
	return new_screen

def get_color_value(color):
	max_channel = max(color)
	value = (max_channel / 255) * 100 # percent
	return value

def set_color_value(color, new_value):
	# value is a percent
	if new_value < 0:
		new_value = 0
	elif new_value > 100:
		new_value = 100
	current_value = get_color_value(color)
	scale = new_value / current_value # multiplier
	new_color = [int(c * scale) for c in color]
	return tuple(new_color)
	
def random_color():
	r = random.randint(0,255)
	g = random.randint(0,255)
	b = random.randint(0,255)
	return (r,g,b)

def create_contrast(color, difference=10, darken_threshold=50):
	# difference - percent value of color goes up or down
	# darken_threshold - lowest value (%) at which new color will become darker in contrast
	r, g, b = color
	max_channel = max(r,g,b) # brightest
	value = (max_channel / 255) * 100

	# lighten - under X % value
	if value < darken_threshold:
		new_value = value + difference
	# darken - above or X % value
	else:
		new_value = value - difference

	if new_value < 0:
		new_value = 0
	if new_value > 255:
		new_value = 255

	# zero error (black)
	if max_channel == 0:
		return (new_value, new_value, new_value)

	# create new color
	scale = ((new_value / 100) * 255) / max_channel # max of new color / old max
	new_color = [int(c * scale) for c in color]
	# correct bounds
	for i in range(3):
		if new_color[i] > 255:
			new_color[i] = 255
		elif new_color[i] < 0:
			new_color[i] = 0
	# final color
	return tuple(new_color)

def change_color(color, index, change):
	new_color = list(color)
	new_color[index] += change
	# apply bounds
	for i in range(3):
		if new_color[i] > 255:
			new_color[i] = 255
		elif new_color[i] < 0:
			new_color[i] = 0
	return tuple(new_color)

def color_to_text(color):
	# return list of text - one for each channel
	# color format: (r, g, b) --> "(r, " | "g, " | "b)" 
	r = "(" + str(color[0]) + ", "
	g = str(color[1]) + ", "
	b = str(color[2]) + ")"
	return [r,g,b]

def text_to_color(text_list):
	# return color tuple
	# inverse of color_to_text
	temp_list = text_list.copy() # preserve original
	for i in range(3):
		temp_list[i] = re.sub("[(), ]+", "", temp_list[i])
	
	color = []
	for c in temp_list:
		try:
			color.append(int(c))
		except:
			color.append(0)
	return tuple(color)


# SETTINGS
class Settings():
	# stores all adjustable program settings
	def __init__(self, maze, player, background):
		# original values (constant)
		self.original_dimensions = [maze.rows, maze.cols]
		self.zoom_level = maze.get_zoom()
		if maze.max_screen_tiles == maze.min_frame_length: # fully zoomed
			self.zoom_level = 0 # maintain full zoom
		# defaults
		self.min_tiles = Maze.MIN_TILES # rows / cols
		self.max_tiles = Maze.MAX_TILES
		self.min_player_speed = Player.MIN_SPEED
		self.max_player_speed = Player.MAX_SPEED
		self.min_player_size = Player.MIN_SIZE
		self.max_player_size = Player.MAX_SIZE
		# maze
		self.maze_dimensions = [maze.rows, maze.cols]
		self.maze_color = maze.bg_color
		self.maze_exit_color = maze.exit_color
		self.maze_line_color = maze.line_color
		# screen
		self.day_color = background.day_color
		self.night_color = background.night_color
		# player
		self.player_color = player.color
		self.player_size = player.size
		self.player_highlight = player.highlight
		self.player_ms_1 = player.ms_1
		self.player_ms_2 = player.ms_2
		self.player_dir_priority = player.dir_priority # 0 - horizontally, 1 - vertically
		self.player_manual_override = player.manual_override
	def randomize_maze(self):
		rows = random.randint(self.min_tiles, self.max_tiles)
		cols = random.randint(self.min_tiles, self.max_tiles)
		self.maze_dimensions = [rows,cols]
	def randomize_player(self):
		if self.min_player_size <= 5: ## don't let player become invisible
			self.min_player_size = 5
		self.player_size = random.randint(self.min_player_size, self.max_player_size)
		self.player_ms_1 = random.randint(self.min_player_speed, self.max_player_speed)
		self.player_ms_2 = random.randint(self.min_player_speed, self.max_player_speed)
		chance = random.randint(1,100)
		if chance <= 50:
			self.player_dir_priority = 0
		else:
			self.player_dir_priority = 1
		chance = random.randint(1,100)
		if chance <= 50:
			self.player_manual_override = False
		else:
			self.player_manual_override = True
	def randomize_all(self):
		self.randomize_maze()
		self.randomize_player()
	def randomize_colors(self, rmaze=True, rplayer=True, rscreen=True):
		if rmaze:
			self.maze_color = random_color()
			self.maze_exit_color = create_contrast(self.maze_color, difference=12, darken_threshold=40)
			self.maze_line_color = random_color()
		if rplayer:
			self.player_color = random_color()
			self.player_highlight = None
		if rscreen:
			self.day_color = random_color()
			self.night_color = random_color()
	def reset_maze(self):
		self.maze_dimensions = [Maze.START_ROWS, Maze.START_COLS]
		self.maze_color = Maze.C_BACKGROUND
		self.maze_exit_color = Maze.C_EXITS
		self.maze_line_color = Maze.C_GRID
	def reset_player(self):
		self.player_color = Player.COLOR
		self.player_highlight = None
		self.player_size = Player.DEFAULT_SIZE
		self.player_ms_1 = Player.DEFAULT_SPEED_1
		self.player_ms_2 = Player.DEFAULT_SPEED_2
		self.player_dir_priority = Player.DIR_PRIORITY
		self.player_manual_override = Player.MANUAL_OVERRIDE
	def reset_all(self):
		self.reset_maze()
		self.reset_player()
	def reset_colors(self, rmaze=True, rplayer=True, rscreen=True):
		if rmaze:
			self.maze_color = Maze.C_BACKGROUND
			self.maze_exit_color = Maze.C_EXITS
			self.maze_line_color = Maze.C_GRID
		if rplayer:
			self.player_color = Player.COLOR
			self.player_highlight = None # null
		if rscreen:
			self.day_color = Background.DAY_COLOR
			self.night_color = Background.NIGHT_COLOR
	def set_color_theme(self, rmaze=True, rplayer=True, rscreen=True): # try to create an appealing palette
		if rmaze:
			self.maze_color = random_color()
			self.maze_exit_color = create_contrast(self.maze_color, difference=12, darken_threshold=40)
			self.maze_line_color = create_contrast(self.maze_color, difference=75, darken_threshold=60)
		if rplayer:
			self.player_color = create_contrast(self.maze_color, difference=45, darken_threshold=90)
			self.player_highlight = None # chosen automatically
		if rscreen:
			self.day_color = create_contrast(self.maze_color, difference=90, darken_threshold=100)
			self.night_color = create_contrast(self.maze_color, difference=75, darken_threshold=0)

# load state
def load_settings(save_state, maze, player, background):
	# maze
	if save_state.maze_dimensions != save_state.original_dimensions: # resized
		maze.resize(save_state.maze_dimensions)
		maze.remap() # must be re-generated
		maze.set_zoom(save_state.zoom_level) # keep same zoom
		player.set_pos(maze.start_cell) # reset player position
		player.escaped = False
	maze.bg_color = save_state.maze_color
	maze.exit_color = save_state.maze_exit_color
	maze.line_color = save_state.maze_line_color
	# screen
	background.day_color = save_state.day_color
	background.night_color = save_state.night_color
	background.choose() # update active color, (updates frame if adaptive)
	background.color_frame(maze.line_color) # will set fixed color (if not adaptive)
	# player
	player.color = save_state.player_color
	player.set_highlight(save_state.player_highlight) # if player_highlight is null, create default (contrast)
	player.size = save_state.player_size
	player.ms_1 = save_state.player_ms_1
	player.ms_2 = save_state.player_ms_2
	player.update_speed() # apply changes
	player.dir_priority = save_state.player_dir_priority
	player.manual_override = save_state.player_manual_override

def get_segments(text):
	# number of pieces of text in a list, or single text
	if isinstance(text, list):
		return len(text)
	else:
		return 1

# SETTINGS MENU
def settings_menu(window, save_state):
	local_fps = 30
	local_clock = pygame.time.Clock()

	# window dimensions
	window_width = window.get_width()
	window_height = window.get_height()

	# window margins
	left_margin = int(7/100 * window_width)
	right_margin = int(7/100 * window_width)
	top_margin = int(5/100 * window_height)
	bottom_margin = int(8/100 * window_height)

	# menu panel dimensions
	menu_width = window_width - left_margin - right_margin
	menu_height = window_height - top_margin - bottom_margin
	menu_rect = (left_margin, top_margin, menu_width, menu_height)
	menu_layer = window.subsurface(menu_rect)

	# custom colors
	c_dim= DIM_GREY
	c_selected = TEXT_YELLOW
	c_active = TEXT_WHITE

	## fonts
	font_scale = 36/900 # font size : window height
	font_size = int(font_scale * window_height)
	menu_font = pygame.font.SysFont("calisto", font_size, bold=False)
	tip_size = int(18/900 * window_height)
	tip_color = DIM_YELLOW
	tip_font = pygame.font.SysFont("consolas", tip_size)

	# text
	size_text = Text("Maze Size", menu_font, c_dim)
	maze_dimensions = MultiText(3 * [""], menu_font, c_dim)
	maze_dimensions.text[1] = " x "

	c_maze_text = Text("Maze Color", menu_font, c_dim)
	rgb_maze = MultiText(3 * [""], menu_font, c_dim)

	c_ends_text = Text("Maze Exits", menu_font, c_dim)
	rgb_ends = MultiText(3 * [""], menu_font, c_dim)

	c_borders_text = Text("Borders", menu_font, c_dim)
	rgb_borders = MultiText(3 * [""], menu_font, c_dim)

	c_day_text = Text("Day Background", menu_font, c_dim)
	rgb_day = MultiText(3 * [""], menu_font, c_dim)

	c_night_text = Text("Night Background", menu_font, c_dim)
	rgb_night = MultiText(3 * [""], menu_font, c_dim)

	c_player_text = Text("Player", menu_font, c_dim)
	rgb_player = MultiText(3 * [""], menu_font, c_dim)

	c_highlight_text = Text("Highlight", menu_font, c_dim)
	rgb_highlight = MultiText(3 * [""], menu_font, c_dim)

	speed_1_text = Text("Movement Speed", menu_font, c_dim)
	speed_1 = Text("", menu_font, c_dim)

	speed_2_text = Text("Shift Speed", menu_font, c_dim)
	speed_2 = Text("", menu_font, c_dim)

	dir_text = Text("Direction Priority", menu_font, c_dim)
	dir_priority = Text("", menu_font, c_dim)

	tap_text = Text("Tap Override", menu_font, c_dim)
	tap_override = Text("", menu_font, c_dim)

	line_text = Text("—", menu_font, c_dim)

	## groups
	option_list = [size_text, c_maze_text, c_ends_text, c_borders_text, c_day_text, c_night_text,
					c_player_text, c_highlight_text, speed_1_text, speed_2_text, dir_text, tap_text]
	attribute_list = [maze_dimensions, rgb_maze, rgb_ends, rgb_borders, rgb_day, rgb_night, 
						rgb_player, rgb_highlight, speed_1, speed_2, dir_priority, tap_override]
	color_option_list = [1,2,3,4,5,6,7] # option indices that handle color values
	toggled_option_list = [10,11] # options that are on/off

	# selectors
	options = len(option_list) # in total
	option_selector = 0 # index
	values = [] # number for each attribute
	for attr in attribute_list:
		pieces = get_segments(attr.text)
		values.append(pieces)
	value_selector = -1 # nothing selected

	# line spacing
	line_space = (menu_height - options * size_text.get_height()) / (options - 1) # to fit all text in menu layer
	if line_space < 0:
		print("Settings Menu Error - cannot fit all text in menu layer")

	# arrange text
	# column 1
	option_list[0].rect.topleft = (0, 0) # first line
	# space out all subsequent lines of text
	for i in range(1, options):
		y = option_list[i-1].rect.bottom + line_space
		option_list[i].rect.topleft = (0, y)

	# middle column (lines / boxes)
	box_length = option_list[0].get_height()
	box_space = 3/100 * window_width # extra space between box and value column
	middle_x = 0 # x value of the box column, update later with values
	
	# tip text
	tip_text = Text("Use arrow keys (↑↓) to change values - hold Ctrl for greater step size", tip_font, tip_color)
	tip_x = left_margin + menu_width/2
	tip_y = window_height - bottom_margin/2
	tip_text.rect.center = (tip_x, tip_y)

	# manual updates
	def update_selected():
		# set proper text color indications
		for i in range(options):
			if i == option_selector:
				if value_selector < 0:
					option_list[i].fg_color = c_active
				else:
					option_list[i].fg_color = c_selected
			else:
				option_list[i].fg_color = c_dim
			# update
			option_list[i].update(resize=False)

			# update values
			current_attribute = attribute_list[i]
			for k in range(values[i]):
				if i == option_selector and k == value_selector:
					value_color = c_active
				else:
					value_color = c_dim
				if isinstance(current_attribute, MultiText):
					current_attribute.fc_list[k] = value_color
				else:
					current_attribute.fg_color = value_color
				# update
				current_attribute.update(resize=False)

	def update_values():
		# load values into text
		maze_dimensions.text[0] = str(save_state.maze_dimensions[0]) # rows
		maze_dimensions.text[2] = str(save_state.maze_dimensions[1]) # cols
		# color format: (r, g, b)
		rgb_maze.text[0], rgb_maze.text[1], rgb_maze.text[2] = color_to_text(save_state.maze_color)
		rgb_ends.text[0], rgb_ends.text[1], rgb_ends.text[2] = color_to_text(save_state.maze_exit_color)
		rgb_borders.text[0], rgb_borders.text[1], rgb_borders.text[2] = color_to_text(save_state.maze_line_color)
		rgb_day.text[0], rgb_day.text[1], rgb_day.text[2] = color_to_text(save_state.day_color)
		rgb_night.text[0], rgb_night.text[1], rgb_night.text[2] = color_to_text(save_state.night_color)
		rgb_player.text[0], rgb_player.text[1], rgb_player.text[2] = color_to_text(save_state.player_color)
		rgb_highlight.text[0], rgb_highlight.text[1], rgb_highlight.text[2] = color_to_text(save_state.player_highlight)
		# speed
		speed_1.text = str(save_state.player_ms_1) + " tiles/sec"
		speed_2.text = str(save_state.player_ms_2) + " tiles/sec"
		# direction
		if save_state.player_dir_priority:
			dir_priority.text = "Up/Down"
		else:
			dir_priority.text = "Left/Right"
		# tap override
		if save_state.player_manual_override:
			tap_override.text = "On"
		else:
			tap_override.text = "Off"

		# update attribute text boxes
		for attr in attribute_list:
			attr.update() # resize rects

		# get column position so that right text is aligned to right margin
		max_attr_width = 0
		for attr in attribute_list:
			if attr.get_width() > max_attr_width:
				max_attr_width = attr.get_width()
		# update column position
		new_middle = menu_width - max_attr_width - box_space - box_length

		# arrange text - column 3
		x = new_middle + box_length + box_space
		# first line
		if isinstance(attribute_list[0], MultiText):
			attribute_list[0].rects[0].topleft = (x, 0)
			attribute_list[0].align_text()
		else:
			attribute_list[0].rect.topleft = (x, 0)
		# subsequent lines
		for i in range(1, options):
			y = option_list[i-1].rect.bottom + line_space
			if isinstance(attribute_list[i], MultiText):
				attribute_list[i].rects[0].topleft = (x, y)
				attribute_list[i].align_text()
			else:
				attribute_list[i].rect.topleft = (x, y)
		return new_middle # box colomn pos

	def set_value(option, value_index, change):
		# RGB values
		if option in color_option_list:
			if option == 1:
				color = save_state.maze_color
				save_state.maze_color = change_color(color, value_index, change)
			elif option == 2:
				color = save_state.maze_exit_color
				save_state.maze_exit_color = change_color(color, value_index, change)
			elif option == 3:
				color = save_state.maze_line_color
				save_state.maze_line_color = change_color(color, value_index, change)
			elif option == 4:
				color = save_state.day_color
				save_state.day_color = change_color(color, value_index, change)
			elif option == 5:
				color = save_state.night_color
				save_state.night_color = change_color(color, value_index, change)
			elif option == 6:
				color = save_state.player_color
				save_state.player_color = change_color(color, value_index, change)
			elif option == 7:
				color = save_state.player_highlight
				save_state.player_highlight = change_color(color, value_index, change)
		# Others
		# maze dimensions
		elif option == 0:
			if value_index == 0:
				save_state.maze_dimensions[0] += change
			elif value_index == 2:
				save_state.maze_dimensions[1] += change
			# bounds
			for i in range(2):
				if save_state.maze_dimensions[i] < save_state.min_tiles:
					save_state.maze_dimensions[i] = save_state.min_tiles
				elif save_state.maze_dimensions[i] > save_state.max_tiles:
					save_state.maze_dimensions[i] = save_state.max_tiles
		# player movement
		elif option == 8:
			save_state.player_ms_1 = int(save_state.player_ms_1 + change) # no fractions unless at max/min
			if save_state.player_ms_1 > save_state.max_player_speed:
				save_state.player_ms_1 = save_state.max_player_speed
			elif save_state.player_ms_1 < save_state.min_player_speed:
				save_state.player_ms_1 = save_state.min_player_speed
		elif option == 9:
			save_state.player_ms_2 = int(save_state.player_ms_2 + change)
			if save_state.player_ms_2 > save_state.max_player_speed:
				save_state.player_ms_2 = save_state.max_player_speed
			elif save_state.player_ms_2 < save_state.min_player_speed:
				save_state.player_ms_2 = save_state.min_player_speed
		# direction priority
		elif option == 10:
			# toggle
			if save_state.player_dir_priority == 1:
				save_state.player_dir_priority = 0
			else:
				save_state.player_dir_priority = 1
		# tap override
		elif option == 11:
			# toggle
			if save_state.player_manual_override:
				save_state.player_manual_override = False
			else:
				save_state.player_manual_override = True

	# get initial selection
	update_selected()
	# load initial values
	middle_x = update_values()

	# controls
	## to move between options
	control_speed = 8 # moves / second
	control_interval = round(local_fps / control_speed) # frames / move
	control_delay = int(0.5 * local_fps)
	cont_control = False
	control_counter = 0
	## to increment values
	attr_speed = 18 # ticks / second
	attr_interval = round(local_fps / attr_speed) # constant speed
	attr_delay = int(0.5 * local_fps) # initial delay
	cont_attr = False # activates constant speed
	attr_counter = 0
	# increment multiplier while holding ctrl
	color_ctrl_boost = 20
	ctrl_boost = 5

	# switches
	menu_switch = True # assume held once opened

	active = True

	while active:
		# keypresses
		keys = pygame.key.get_pressed()
		mods = pygame.key.get_mods()
		ctrl_held = (mods & pygame.KMOD_CTRL)

		if ctrl_held and keys[pygame.K_q]: # exit
			pygame.quit()
			sys.exit(0)

		if ctrl_held and keys[pygame.K_o]: # close settings menu
			if not menu_switch:
				menu_switch = True
				active = False
		elif keys[pygame.K_ESCAPE] or keys[pygame.K_BACKSPACE]: # go back
			if not menu_switch:
				menu_switch = True
				if value_selector > -1:
					value_selector = -1
					update_selected()
				else:
					active = False # close menu
		else:
			menu_switch = False

		# --- Arrow Keys ---
		# Set Values
		value_switch = False
		if value_selector > -1 and (keys[pygame.K_UP] or keys[pygame.K_DOWN]):
			value_switch = True
			if option_selector not in toggled_option_list: # not toggled
				if attr_counter <= 0:
					# add delay
					if cont_attr:
						attr_counter = attr_interval
					else:
						attr_counter = attr_delay
						cont_attr = True # constant speed after this
					change = 0 # amount added to the selected value
					if keys[pygame.K_UP]:
						change = 1
					elif keys[pygame.K_DOWN]:
						change = -1
					# boost
					if ctrl_held:
						if option_selector in color_option_list:
							change *= color_ctrl_boost
						else:
							change *= ctrl_boost
					# apply change to save data
					set_value(option_selector, value_selector, change)
					# update screen values
					middle_x = update_values()
				else: # tick
					attr_counter -= 1
		else: # released
			cont_attr = False # delay again
			attr_counter = 0 # manual control

		# Switch Options
		# activated button for switching an option
		select_option_btn = False
		select_attribute_btn = False

		# check button states
		if not value_switch: # cannot change options while setting values
			if value_selector < 0 and (keys[pygame.K_UP] or keys[pygame.K_DOWN]): # option
				select_option_btn = True
			if keys[pygame.K_LEFT] or keys[pygame.K_RIGHT]: # attribute
				select_attribute_btn = True

		# get selection
		if select_attribute_btn or select_option_btn:
			if control_counter <= 0:
				# delay
				if cont_control:
					control_counter = control_interval
				else:
					control_counter = control_delay
					cont_control = True

				# Select Attribute
				if select_attribute_btn:
					# deselect current value (if selected)
					if value_selector > -1:
						current_attribute = attribute_list[option_selector]
						if isinstance(current_attribute, MultiText):
							current_attribute.fc_list[value_selector] = c_dim
						else:
							current_attribute.fg_color = c_dim
						current_attribute.update(resize=False)
					# determine how far the selection will move
					selection_jump = 1
					if option_selector == 0 and (value_selector == 0 or value_selector == 2):
						selection_jump = 2 # for dimension values
					# move selection
					if keys[pygame.K_LEFT]:
						value_selector -= selection_jump
					if keys[pygame.K_RIGHT]:
						value_selector += selection_jump
					# restrict bounds - hard stop
					if value_selector < -1:
						value_selector = -1
					elif value_selector > (values[option_selector] - 1):
						value_selector = values[option_selector] - 1
					# update option text
					if value_selector < 0:
						option_list[option_selector].fg_color = c_active
					else: # in sub-menu
						option_list[option_selector].fg_color = c_selected
					option_list[option_selector].update(resize=False)
					# update selected value (if selected)
					if value_selector > -1:
						current_attribute = attribute_list[option_selector]
						if isinstance(current_attribute, MultiText):
							current_attribute.fc_list[value_selector] = c_active
						else:
							current_attribute.fg_color = c_active
						current_attribute.update(resize=False)
						# highlight tip text
						tip_text.fg_color = c_selected
						tip_text.update(resize=False)
					else:
						tip_text.fg_color = tip_color
						tip_text.update(resize=False)

				# Select Item
				elif select_option_btn:
						# deselect current item
						option_list[option_selector].fg_color = c_dim
						option_list[option_selector].update(resize=False)
						# move selection
						if keys[pygame.K_UP]:
							option_selector -= 1
						if keys[pygame.K_DOWN]:
							option_selector += 1
						# restrict bounds - wrap around
						if option_selector < 0:
							option_selector = options - 1
						elif option_selector > (options - 1):
							option_selector = 0
						# update selected option
						option_list[option_selector].fg_color = c_active
						option_list[option_selector].update(resize=False)
			# tick counter
			else:
				control_counter -= 1
		else:
			cont_control = False
			control_counter = 0 # manual

		# Events - must be called to process internal event handlers
		for event in pygame.event.get():
			if event.type == pygame.QUIT:
				pygame.quit()
				sys.exit(0)

			if event.type == pygame.KEYDOWN:
				# Set Toggled Values
				if value_selector > -1 and (event.key == pygame.K_UP or event.key == pygame.K_DOWN):
					if option_selector in toggled_option_list:
						# apply change to save data
						set_value(option_selector, value_selector, 1)
						# update screen values
						middle_x = update_values()
		
		# Display
		window.fill(BLACK)
		# add text
		for left_text in option_list:
			left_text.draw(menu_layer)
		for right_text in attribute_list:
			right_text.draw(menu_layer)
		# draw lines
		for i in range(options):
			if i not in color_option_list:
				next_y = option_list[i].rect.top
				line_text.rect.topleft = (middle_x, next_y)
				if i == option_selector:
					if value_selector > -1:
						line_text.fg_color = c_selected
					else:
						line_text.fg_color = c_active
				else:
					line_text.fg_color = c_dim
				line_text.update(resize=False)
				line_text.draw(menu_layer)
		# draw color boxes
		for i in color_option_list:
			rect = (middle_x, option_list[i].rect.top, box_length, box_length)
			color = text_to_color(attribute_list[i].text)
			pygame.draw.rect(menu_layer, color, rect)
			if i == option_selector:
				if value_selector > -1:
					pygame.draw.rect(menu_layer, c_selected, rect, width=2)
				else:
					pygame.draw.rect(menu_layer, c_active, rect, width=2)
			else:
				pygame.draw.rect(menu_layer, c_dim, rect, width=2)
		# tip
		tip_text.draw(window)

		# refresh screen
		pygame.display.update()
		local_clock.tick(local_fps)
	return

# SAVE MENU
def save_menu(window, maze, background, prompt_str="File Path:  ", save_mode=1):
	# SAVE MODE 0 - FILE
	# SAVE MODE 1 - DIRECTORY
	file_extension = "." + IMAGE_FORMAT

	local_fps = 30
	local_clock = pygame.time.Clock()

	# window dimensions
	window_width = window.get_width()
	window_height = window.get_height()

	# window margins
	left_margin = int(9/100 * window_width)
	right_margin = int(9/100 * window_width)
	top_margin = int(12/100 * window_height)
	bottom_margin = int(7/100 * window_height)

	# menu panel dimensions
	menu_width = window_width - left_margin - right_margin
	menu_height = window_height - top_margin - bottom_margin
	menu_rect = (left_margin, top_margin, menu_width, menu_height)

	# option panel dimensions (menu - message box)
	option_width = menu_width
	option_height = menu_height * 0.70
	option_x = menu_rect[0]
	option_y = menu_rect[1]
	option_rect = (option_x, option_y, option_width, option_height)
	option_layer = window.subsurface((option_rect))

	# message box dimensions
	box_width = menu_width
	box_height = menu_height - option_height
	box_x = menu_rect[0]
	box_y = menu_rect[1] + menu_height - box_height # anchor bottom
	box_rect = (box_x, box_y, box_width, box_height)
	message_layer = window.subsurface(box_rect)

	# custom colors
	c_prompt = TEXT_YELLOW
	c_text = TEXT_WHITE
	c_dim = DIM_GREY
	c_error = ERROR_RED
	c_success = SUCCESS_GREEN

	## fonts
	large_size = int(45/900 * window_height) # font size : window height
	medium_size = int(32/900 * window_height)
	small_size = int(20/900 * window_height)
	text_font = pygame.font.SysFont("calibri", large_size)
	tip_font = pygame.font.SysFont("consolas", large_size)
	small_font = pygame.font.SysFont("consolas", small_size)

	# space between rows of text
	line_space = option_height * 10/100

	# prompt
	file_prompt = Text(prompt_str, text_font, c_prompt)
	file_prompt.rect.topleft = (0,0)

	# file text
	special_chars = "._ !@#$%^&()"
	file_box = MultiText(2 * [""], text_font, c_text)
	file_x = file_prompt.get_width()
	file_y = 0

	# color option
	color_preference = 1 # indicates colored, 0 = black and white
	color_prompt = Text("Color", text_font, c_prompt)
	color_prompt.rect.topleft = (0, file_prompt.rect.bottom + line_space)

	# check box
	check_margin = 25 # between prompt and check box
	check_box_width = 3
	check_box_rect = pygame.Rect(color_prompt.rect.right + check_margin, color_prompt.rect.top, 
				color_prompt.get_height(), color_prompt.get_height())
	cross_padding = check_box_rect.width * 25/100
	cross_rect = pygame.Rect(check_box_rect.left + cross_padding, check_box_rect.top + cross_padding,
							check_box_rect.width - 2 * cross_padding, check_box_rect.height - 2 * cross_padding)
	c_check_box = c_dim
	check_box_active = False # hovered

	# color description
	color_states = ["Maze will be saved in black & white.", "Maze will be saved in color."]
	if save_mode == 1:
		for i in range(2): # make plural
			color_states[i] = color_states[i].replace("Maze", "Mazes")
	color_description = Text("", small_font, c_dim)
	color_description_pos = (check_box_rect.right + check_margin, color_prompt.rect.bottom - color_description.get_height())
	color_description.rect.topleft = color_description_pos

	## amount option
	min_saves = 1
	max_saves = 100
	num_saves = 5 # current
	incr_ctrl_boost = 10 # while holding ctrl
	incr_speed = 20 # increments / sec
	incr_interval = round(local_fps / incr_speed) # frames per increment when continuous
	incr_delay = int(0.5 * local_fps) # frames until incrementing is continuous
	continuous_incr = False
	incr_counter = 0

	# amount prompt
	amount_prompt = Text("How many do you want?", text_font, c_prompt)
	amount_prompt.rect.topleft = (0, color_prompt.rect.bottom + line_space)

	# amount box
	amount_margin = 25 # between prompt and amount box
	amount_box = Text(str(num_saves), text_font, c_text)
	amount_box_pos = (amount_prompt.rect.right + amount_margin, amount_prompt.rect.top)

	# tips
	tip_text = Text("Esc to cancel | Enter to save", tip_font, c_text)
	tip_text.rect.topleft = (option_width/2 - tip_text.get_width()/2, option_height - tip_text.get_height() - line_space)

	# message box
	message_box = Text("", small_font, c_error)

	# cursor
	cursor_text = "|"
	cursor_speed = 1 # blinks per second
	cursor_delay = round(local_fps / cursor_speed) # frames per blink
	cursor_counter = 0

	## delete option
	delete_speed = 20 # chars per second
	delete_interval = round(local_fps / delete_speed) # frames until another char is deleted
	delete_delay = int(0.5 * local_fps) # wait time (in frames) until deleting becomes continous
	continuous_delete = False # hold to keep deleting
	delete_counter = 0

	## freeze screen after attempting to save
	freeze_time = 1
	freeze_delay = int(local_fps * freeze_time)
	freeze_counter = freeze_delay

	# switches
	menu_switch = True # held once opened
	enter_switch = False
	error_switch = False
	save_switch = False

	active = True

	while active:
		# keypresses
		keys = pygame.key.get_pressed()
		mods = pygame.key.get_mods()
		mouse_x, mouse_y = pygame.mouse.get_pos()
		ctrl_held = (mods & pygame.KMOD_CTRL)

		# exit
		if ctrl_held and keys[pygame.K_q]:
			pygame.quit()
			sys.exit(0)

		# close menu
		if keys[pygame.K_ESCAPE]:
			if not menu_switch:
				menu_switch = True
				active = False
		else:
			menu_switch = False

		# submit (enter)
		if keys[pygame.K_RETURN]:
			if enter_switch == False:
				enter_switch = True
				# check if the file / directory can be created
				filename = file_box.text[0]
				if save_mode == 0:
					filename += file_extension
				error_msg = "" # catch errors
				if not file_box.text[0] or file_box.text[0].isspace(): # only spaces
					error_msg = "Must enter a valid path!"
				elif os.path.exists(filename): # already exists
					error_msg = "Cannot create a file when that file already exists: \'" + file_box.text[0] + "\'"
				else:
					# try to create file
					try:
						# create a temporary, blank file with the desired name
						f = open(filename, "x")
						f.close()
						os.remove(filename) # delete temp file
						save_switch = True # successfully reserved file path
						active = False # close menu
					except Exception as e:
						error_msg = str(e)
				# acknowledge errors
				if error_msg:
					error_switch = True
					message_box.text = error_msg
		else:
			enter_switch = False

		# attempt to save the maze
		if save_switch == True:
			## minimum side length of image
			min_size = 1000
			c_frame = background.frame_color
			w_frame = background.border_size
			try:
				# save current
				if save_mode == 0:
					path = file_box.text[0] + file_extension
					maze.save_image(path, color_preference, frame_width=w_frame, frame_color=c_frame, size=min_size, bound=0)
				# save many
				else:
					directory = file_box.text[0]
					os.mkdir(directory) # create folder
					for i in range(num_saves):
						filename = "Maze_" + str(i+1) + file_extension # name of next maze
						new_path = os.path.join(directory, filename)
						maze.save_image(new_path, color_preference, frame_width=w_frame, frame_color=c_frame, size=min_size, bound=0)
						maze.remap() # generate new maze
				# successfully saved
			except Exception as e:
				# show error
				message_box.text = str(e)
				error_switch = True

		# delete characters
		if keys[pygame.K_BACKSPACE] and not save_switch: # remove button
			if delete_counter <= 0 and len(file_box.text[0]) > 0:
				# add delay
				if continuous_delete:
					delete_counter = delete_interval
				else: # first delete
					delete_counter = delete_delay
					continuous_delete = True
				file_box.text[0] = file_box.text[0][:-1]
				# always show cursor when backspacing
				cursor_counter = 0
				# reset error
				if error_switch:
					error_switch = False
			else: # tick
				delete_counter -= 1
		else:
			delete_counter = 0 # ready to delete again immediately
			continuous_delete = False # released

		# clear all
		if ctrl_held and keys[pygame.K_BACKSPACE]:
			file_box.text[0] = ""

		# increment amount
		if save_mode == 1:
			# increment button
			if (keys[pygame.K_UP] or keys[pygame.K_DOWN]) and not save_switch:
				if incr_counter <= 0:
					# add delay
					if continuous_incr:
						incr_counter = incr_interval
					else: # first hit
						incr_counter = incr_delay
						continuous_incr = True
					increment = 0 # increase amount by this much
					if keys[pygame.K_UP]:
						increment = 1
					else:
						increment = -1
					# boost
					if ctrl_held:
						increment *= incr_ctrl_boost
					# increment
					num_saves += increment
					# apply bounds
					if num_saves < min_saves:
						num_saves = min_saves
					elif num_saves > max_saves:
						num_saves = max_saves
				else: # tick
					incr_counter -= 1
			else: # released
				incr_counter = 0
				continuous_incr = False

		# set check box state
		check_box_active = False
		# within check box horizontally + vertically
		if mouse_x > (option_x + check_box_rect.left) and mouse_x < (option_x + check_box_rect.right):
			if mouse_y > (option_y + check_box_rect.top) and mouse_y < (option_y + check_box_rect.bottom):
				check_box_active = True

		# set check box color (and description color)
		if check_box_active:
			c_check_box = c_text
			color_description.fg_color = c_check_box
			#pygame.mouse.set_cursor(pygame.cursors.diamond) # change cursor when hovering
		else:
			c_check_box = c_dim
			color_description.fg_color = c_check_box
			#pygame.mouse.set_cursor(pygame.SYSTEM_CURSOR_ARROW)

		# remove cursor while calculating size of file
		file_box.text[1] = cursor_text
		file_box.update()

		# events
		for event in pygame.event.get():
			if event.type == pygame.QUIT:
				pygame.quit()
				sys.exit(0)
			# typing
			if event.type == pygame.KEYDOWN and not save_switch:
				new_char = event.unicode
				# check valid character
				if new_char != "" and (new_char.isalnum() or new_char in special_chars):
					# check if character can fit in line
					char_box = Text(new_char, text_font, c_text)
					if file_x + file_box.get_width() + char_box.get_width() < option_width:
						file_box.text[0] += new_char
						# always show cursor when typing
						cursor_counter = 0
						# reset error
						if error_switch:
							error_switch = False
			# mouse click
			if event.type == pygame.MOUSEBUTTONDOWN and not save_switch:
				mouse_state = pygame.mouse.get_pressed()
				if mouse_state[0]: # left click
					if check_box_active: # hovered
						color_preference = 1 if color_preference == 0 else 0 # toggle box

		# tick cursor counter
		if cursor_counter > 0:
			cursor_counter -=1
		else:
			cursor_counter = cursor_delay

		# set cursor state
		if cursor_counter <= math.ceil(cursor_delay/2):
			# on screen for half the cycle
			file_box.text[1] = ""
		else:
			# off screen for other half
			file_box.text[1] = cursor_text

		# update file box
		if error_switch or save_switch: # tried to save
			file_box.color_all(c_dim)
		else:
			file_box.color_all(c_text)
		file_box.update()
		file_box.rects[0].topleft = (file_x, file_y)
		file_box.align_text()

		# update color description
		color_description.text = color_states[color_preference]
		color_description.update(resize=False)

		# update amount box
		if save_mode == 1:
			amount_box.text = str(num_saves)
			amount_box.update()
			amount_box.rect.topleft = amount_box_pos

		# update message box
		if error_switch:
			message_box.fg_color = c_error
		elif save_switch:
			filename = file_box.text[0] 
			if save_mode == 0:
				filename += file_extension
			saving_text = "Saving " + filename + "..."
			message_box.text = saving_text
			message_box.fg_color = c_success
		elif save_mode == 1: # tip
			message_box.text = "Use arrow keys to increment amount."
			message_box.fg_color = c_prompt
		message_box.update()
		msg_x = box_width/2 - message_box.get_width() / 2
		msg_y = box_height/2 - message_box.get_height() / 2
		if msg_x < 0:
			msg_x = 0
		message_box.rect.topleft = (msg_x, msg_y)

		# draw
		window.fill(BLACK)
		# text
		file_prompt.draw(option_layer)
		file_box.draw(option_layer)
		color_prompt.draw(option_layer)
		color_description.draw(option_layer)
		if save_mode == 1:
			amount_prompt.draw(option_layer)
			amount_box.draw(option_layer)
		tip_text.draw(option_layer)
		# message box
		message_box.draw(message_layer)
		# check box
		pygame.draw.rect(option_layer, c_check_box, check_box_rect, check_box_width)
		if color_preference:
			# check the box
			pygame.draw.line(option_layer, c_check_box, cross_rect.topleft, cross_rect.bottomright, check_box_width)
			pygame.draw.line(option_layer, c_check_box, cross_rect.topright, cross_rect.bottomleft, check_box_width)

		# refresh screen
		pygame.display.update()
		local_clock.tick(local_fps)

	# make sure save screen is shown
	if save_switch:
		freeze_counter = freeze_delay
		while (freeze_counter > 0):
			freeze_counter -= 1
			pygame.event.pump() # internal processes
			local_clock.tick(local_fps)
	return

# CONTROLS MENU
def controls_menu(window, start_page=2):
	local_fps = 30
	local_clock = pygame.time.Clock()

	# window dimensions
	window_width = window.get_width()
	window_height = window.get_height()

	# window margins
	left_margin = int(3/100 * window_width)
	right_margin = int(3/100 * window_width)
	top_margin = int(3/100 * window_height)
	bottom_margin = int(3/100 * window_height)

	# gap between different panels
	panel_gap = int(4/100 * window_height)

	# title panel
	title_width = window_width - left_margin - right_margin
	title_height = int(7/100 * window_height)
	title_rect = (left_margin, top_margin, title_width, title_height)
	title_layer = window.subsurface(title_rect)

	# index panel
	index_width = window_width - left_margin - right_margin
	index_height = int(5/100 * window_height)
	index_y = int(window_height - bottom_margin - index_height)
	index_rect = (left_margin, index_y, index_width, index_height)
	index_layer = window.subsurface(index_rect)

	# menu panel
	menu_width = window_width - left_margin - right_margin
	menu_height = window_height - top_margin - bottom_margin - title_height - (panel_gap*2) - index_height
	menu_y = top_margin + title_height + panel_gap
	menu_radius = int(0.10 * menu_height)
	menu_rect = (left_margin, menu_y, menu_width, menu_height)
	menu_layer = window.subsurface(menu_rect)

	# custom colors
	c_title = TEXT_YELLOW
	c_text = TEXT_WHITE
	c_background = (0,12,12)

	# fonts
	title_size = int(45/900 * window_height)
	text_size = int(32/900 * window_height)
	small_size = int(20/900 * window_height)
	title_font = pygame.font.SysFont("calisto", title_size)
	text_font = pygame.font.SysFont("calisto", text_size)
	page_font = pygame.font.SysFont("consolas", small_size)

	# controls text
	menu_group = ["Esc = Controls Menu",
				"Ctrl + O = Options Menu",
				"Ctrl + S = Save Current",
				"Ctrl + Alt + S = Save Many"]
				
	button_group = ["G = Generate New Maze",
					"P = Toggle Play Mode",
					"F = Toggle Fullscreen",
					"Ctrl + V = Toggle Adaptive Lines",
					"Ctrl + B = Toggle Adaptive Frame",
					"N = Swap Day / Night Background",
					"R = Reset View / Player",
					"Ctrl + Q = Quit"]

	setting_group = ["Ctrl + R = Reset All",
					"Alt + R = Reset Colors",
					"Ctrl + M = Random Maze Dimensions",
					"Alt + M = Random Maze Colors",
					"Alt + N = Random Background Colors",
					"Ctrl + P = Random Player Settings",
					"Alt + P = Random Player Colors",
					"Alt + T = Set Color Theme"]

	view_group = ["Arrow Keys = Pan",
				"Mouse Wheel = Scroll",
				"Ctrl + Mouse Wheel = Zoom",
				"Ctrl + Plus / Minus = Zoom in Steps",
				"1 = Jump To Quadrant 1",
				"2 = Jump To Quadrant 2",
				"3 = Jump To Quadrant 3",
				"4 = Jump To Quadrant 4",
				"5 = Jump to Center"]

	play_group = ["Arrow Keys = Move",
				"Caps Lock = Switch To Alternate Speed",
				"Shift = Temporarily Switch Speed",
				"Alt + Mouse Wheel = Grow / Shrink Player",
				"Alt + Plus / Minus = Resize Player",
				"1 = Teleport To Start",
				"2 = Teleport To Finish (once escaped)",
				"3 = Random Teleport (once escaped)"]

	zoom_group = ["Ctrl + 0 = Reset Zoom",
				"Ctrl +  ] = Max Zoom",
				"Ctrl +  [ = Min Zoom",
				"Alt + 0 = Reset Player Size",
				"Alt +  ] = Max Player Size",
				"Alt +  [ = Min Player Size"]

	line_group = ["V + ] = Max Line Width",
				"V + [ = Min Line Width",
				"V + 0 = Reset Line Width",
				"V + Plus / Minus = Resize Lines in Steps",
				"V + Mouse Wheel = Resize Lines"]

	border_group = ["B + ] = Max Border Size",
					"B + [ = Min Border Size",
					"B + 0 = Reset Border Size",
					"B + Plus / Minus = Resize Borders",
					"B + Mouse Wheel = Resize Borders in Steps"]

	# pages
	page_list = [menu_group, button_group, setting_group, view_group, play_group, zoom_group, line_group, border_group]
	page_titles = ["Menu Group", "Button Group", "Setting Group", "In View Mode", "In Play Mode", "Zoom Group", "Line Group", "Frame Group"]
	total_pages = len(page_list)
	page_selector = start_page - 1 # index of page
	if page_selector < 0:
		page_selector = 0
	elif page_selector >= total_pages:
		page_selector = total_pages - 1
	page_box = Text("", page_font, c_text) # shows current page

	# page bar
	page_bar_margin = int(15/100 * index_width)
	page_bar_radius = int(index_width)
	page_bar_rect = (page_bar_margin, 0, index_width - (page_bar_margin * 2), index_height)

	# text
	key_list = [] # all key combinations on current page
	description_list = [] # all key descriptions on current page
	row_list = [] # y values of text lines, extra lines simply will not be drawn
	title_box = Text("", title_font, c_title)

	## text spacing + position
	line_space = int(36/900 * window_height) # between rows
	column_space = int(55/1128 * menu_width) # between center and columns
	text_center = (menu_width * 0.45) # where the center of the two text columns is
	separator_text = Text("=", text_font, c_text) # symbol between key and description

	# arrows
	arrow_height = int(index_height * 80/100)
	arrows_selected = [0,0] # determines if the left or right arrow is selected
	arrow_images = []
	for image_surf in [L_ARROW, SL_ARROW, R_ARROW, SR_ARROW]:
		scale = arrow_height / image_surf.get_height()
		new_width = image_surf.get_width() * scale
		new_height = image_surf.get_height() * scale
		new_arrow = image_surf.copy().convert_alpha() # image surface
		new_arrow = pygame.transform.scale(new_arrow, (new_width, new_height))
		arrow_images.append(new_arrow)

	# switches
	menu_switch = True
	l_arrow_switch = False
	r_arrow_switch = False
	change_page = True # must update text

	active = True

	while active:
		# keypresses
		keys = pygame.key.get_pressed()
		mods = pygame.key.get_mods()
		ctrl_held = (mods & pygame.KMOD_CTRL)

		# exit
		if ctrl_held and keys[pygame.K_q]:
			pygame.quit()
			sys.exit(0)

		# close menu
		if keys[pygame.K_ESCAPE]:
			if not menu_switch:
				menu_switch = True
				active = False
		else:
			menu_switch = False

		# previous page
		if keys[pygame.K_LEFT]:
			arrows_selected[0] = 1
			if not l_arrow_switch:
				l_arrow_switch = True
				page_selector -= 1
				if page_selector < 0:
					page_selector = 0
				else:
					change_page = True
		else:
			l_arrow_switch = False
			arrows_selected[0] = 0

		# next page
		if keys[pygame.K_RIGHT]:
			arrows_selected[1] = 1
			if not r_arrow_switch:
				r_arrow_switch = True
				page_selector += 1
				if page_selector > (total_pages - 1):
					page_selector = total_pages - 1
				else:
					change_page = True
		else:
			r_arrow_switch = False
			arrows_selected[1] = 0

		# events
		for event in pygame.event.get():
			if event.type == pygame.QUIT:
				pygame.quit()
				sys.exit(0)

		# update page
		if change_page:
			change_page = False

			# reset
			key_list = []
			description_list = []
			row_list = []

			# extract text
			for text in page_list[page_selector]:
				key_text, description_text = text.split("=")
				key_box = Text(key_text, text_font, c_text)
				description_box = Text(description_text, text_font, c_text)
				key_list.append(key_box)
				description_list.append(description_box)

			# count rows
			num_rows = len(key_list)
			row_height = key_list[0].get_height()

			# offset to align rows in the center of the menu layer
			offset_y = (menu_height/2) - ((row_height * num_rows) + (line_space * (num_rows-1))) / 2

			# get row positions
			for i in range(num_rows):
				y = i * (row_height + line_space) + offset_y
				row_list.append(y)

			# arrange text - keys to the left, description to the right
			for i in range(num_rows):
				y = row_list[i]
				# key
				kx = text_center - (separator_text.get_width()/2) - key_list[i].get_width() - column_space
				key_list[i].rect.topleft = (kx,y)
				# description
				dx = text_center + (separator_text.get_width()/2) + column_space
				description_list[i].rect.topleft = (dx,y)
			
			# update title
			title_box.text = page_titles[page_selector]
			title_box.update()
			title_box_pos = (0, title_height/2 - title_box.get_height()/2)
			title_box.rect.topleft = title_box_pos ## anchor topleft

		# update arrows
		left_arrow = arrow_images[0 + arrows_selected[0]]
		left_arrow_pos = (0, index_height/2 - left_arrow.get_height()/2)
		right_arrow = arrow_images[2 + arrows_selected[1]]
		right_arrow_pos = (index_width - right_arrow.get_width(), index_height/2 - right_arrow.get_height()/2)

		# update page text
		page_box.text = "Page " + str(page_selector + 1) + "/" + str(total_pages)
		page_box.update()
		# center
		page_box_pos = (index_width/2, index_height/2) 
		page_box.rect.center = page_box_pos

		# draw
		window.fill(BLACK)
		#menu_layer.fill(c_background)
		pygame.draw.rect(window, c_background, menu_rect, border_radius=menu_radius)
		# title panel
		title_box.draw(title_layer)
		# main panel
		for key_box in key_list:
			key_box.draw(menu_layer)
		for description_box in description_list:
			description_box.draw(menu_layer)
		for y in row_list:
			separator_text.rect.midtop = (text_center, y)
			separator_text.draw(menu_layer)
		# index panel
		index_layer.blit(left_arrow, left_arrow_pos)
		index_layer.blit(right_arrow, right_arrow_pos)
		pygame.draw.rect(index_layer, c_background, page_bar_rect, border_radius=page_bar_radius)
		page_box.draw(index_layer)
		# update screen
		pygame.display.update()
		local_clock.tick(local_fps)

# MAIN
def main():
	pygame.display.set_caption("Maze Generator")
	pygame.display.set_icon(MAZE_ICON)

	screen_init() # ensure window can fit on screen
	screen = pygame.display.set_mode(WIN_SIZE)
	clock = pygame.time.Clock()
	fps = 60

	# create background (of screen)
	new_background = Background(fps)

	# create maze
	maze_seed = [0,0]
	new_maze = Maze((Maze.START_ROWS, Maze.START_COLS), fps)
	new_maze.remap(maze_seed)

	# create player
	new_player = Player(Player.COLOR, fps)
	new_player.set_pos(new_maze.start_cell)

	# switches - must be manually pressed each time
	a_switch = False
	b_switch = False
	f_switch = False
	g_switch = False
	m_switch = False
	n_switch = False
	p_switch = False
	r_switch = False
	t_switch = False
	v_switch = False
	one_switch = False
	two_switch = False
	three_switch = False
	player_size_switch = False
	border_switch = False
	line_switch = False
	zoom_switch = False
	menu_switch = False # came from menu

	# toggles
	fullscreen = False
	playing = False

	active = True

	while active:
		# KEYS PRESSED
		keys = pygame.key.get_pressed()
		mods = pygame.key.get_mods() # bitmask
		ctrl_held = (mods & pygame.KMOD_CTRL)
		alt_held = alt_held = (mods & pygame.KMOD_ALT)
		shift_held = (mods & pygame.KMOD_SHIFT)
		caps_lock = (mods & pygame.KMOD_CAPS)
		b_held = keys[pygame.K_b]
		v_held = keys[pygame.K_v]

		# EXIT
		if ctrl_held and keys[pygame.K_q]:
			active = False

		# CONTROLS
		if keys[pygame.K_ESCAPE]:
			if not menu_switch:
				menu_switch = True
				controls_menu(screen)

		# SETTINGS
		elif ctrl_held and keys[pygame.K_o]:
			if not menu_switch:
				menu_switch = True
				state = Settings(new_maze, new_player, new_background)
				settings_menu(screen, state)
				load_settings(state, new_maze, new_player, new_background)

		# SAVE
		elif ctrl_held and keys[pygame.K_s]:
			if not menu_switch:
				menu_switch = True
				mode = 0 # single
				prompt = "Enter Filename:  "
				if alt_held:
					mode = 1 # save many
					prompt = "Enter Folder:  "
				save_menu(screen, new_maze, new_background, prompt, mode)

		else: # RESET MENU SWITCH
			menu_switch = False # all menu buttons released

		# TOGGLE FULLSCREEN
		if keys[pygame.K_f]:
			if not f_switch:
				f_switch = True
				if fullscreen:
					screen = exit_fullscreen()
					fullscreen = False
				else:
					screen = enter_fullscreen()
					fullscreen = True
				new_maze.resize() # adjust maze window location
		else:
			f_switch = False

		# PLAYER KEY
		if keys[pygame.K_p]:
			if not p_switch:
				p_switch = True
				# RANDOMIZE PLAYER
				if ctrl_held:
					state = Settings(new_maze, new_player, new_background)
					state.randomize_player()
					load_settings(state, new_maze, new_player, new_background)
				# RANDOM PLAYER COLOR
				if alt_held:
					state = Settings(new_maze, new_player, new_background)
					state.randomize_colors(0, 1, 0)
					load_settings(state, new_maze, new_player, new_background)
				# TOGGLE PLAY MODE
				if not ctrl_held and not alt_held:
					if playing:
						playing = False
					else:
						playing = True
						#new_player.set_pos(new_maze.start_cell) ## restart automatically
		else:
			p_switch = False

		# GENERATE
		if keys[pygame.K_g]:
			if not g_switch:
				g_switch = True
				new_maze.remap(maze_seed)
				new_player.set_pos(new_maze.start_cell)
				new_player.escaped = False # new map
		else:
			g_switch = False

		# ALIGN
		if keys[pygame.K_a] and not playing:
			if not a_switch:
				new_maze.align_frame()
				a_switch = True
		else:
			a_switch = False

		# BACKGROUND
		if keys[pygame.K_n]:
			if not n_switch:
				n_switch = True
				# RANDOMIZE
				if alt_held:
					state = Settings(new_maze, new_player, new_background)
					state.randomize_colors(0, 0, 1)
					load_settings(state, new_maze, new_player, new_background)
				# SWAP
				else:
					new_background.toggle()
		else:
			n_switch = False

		# RANDOMIZE MAZE
		if keys[pygame.K_m]:
			if not m_switch:
				m_switch = True
				# ENVIRONMENT
				if ctrl_held:
					state = Settings(new_maze, new_player, new_background)
					state.randomize_maze()
					load_settings(state, new_maze, new_player, new_background)
				# COLORS
				elif alt_held:
					state = Settings(new_maze, new_player, new_background)
					state.randomize_colors(1, 0, 0)
					load_settings(state, new_maze, new_player, new_background)
		else:
			m_switch = False

		# COLOR THEME
		if alt_held and keys[pygame.K_t]:
			if not t_switch:
				t_switch = True
				state = Settings(new_maze, new_player, new_background)
				state.set_color_theme(1, 1, 1) # colors will be closely related
				load_settings(state, new_maze, new_player, new_background)
		else:
			t_switch = False

		# RESET
		if keys[pygame.K_r]:
			if not r_switch:
				r_switch = True
				# ENVIRONMENT
				if ctrl_held: # ctrl
					state = Settings(new_maze, new_player, new_background)
					state.reset_all()
					load_settings(state, new_maze, new_player, new_background)
				# COLOR
				if alt_held: # alt - reset color
					state = Settings(new_maze, new_player, new_background)
					state.reset_colors()
					load_settings(state, new_maze, new_player, new_background)
				# SOFT RESET
				if not ctrl_held and not alt_held:
					if playing: # PLAYER
						new_player.set_pos(new_maze.start_cell)
						new_player.escaped = False
					else: # VIEW
						new_maze.set_frame_center(new_maze.start_cell)
		else:
			r_switch = False

		# LINE SHORTCUTS
		if v_held and (keys[pygame.K_0] or keys[pygame.K_RIGHTBRACKET] or keys[pygame.K_LEFTBRACKET]):
			if not line_switch and not new_maze.adaptive_lines:
				line_switch = True
				if keys[pygame.K_0]: # default lines
					new_maze.line_width = Maze.DEFAULT_LINE_WIDTH
				elif keys[pygame.K_RIGHTBRACKET]: # max line width
					new_maze.line_width = Maze.MAX_LINE_WIDTH
				elif keys[pygame.K_LEFTBRACKET]: # min line width
					new_maze.line_width = Maze.MIN_LINE_WIDTH
		else:
			line_switch = False

		# RESIZE LINES
		line_dir = 0
		if v_held:
			if keys[pygame.K_EQUALS]:
				line_dir = 1
			elif keys[pygame.K_MINUS]:
				line_dir = -1
		new_maze.expand_lines(line_dir)

		# TOGGLE ADAPTIVE LINES
		if ctrl_held and v_held:
			if not v_switch:
				v_switch = True
				new_maze.toggle_adaptive_lines()
				if new_maze.adaptive_lines:
					new_maze.update_line_size() # set adaptive size
		else:
			v_switch = False

		# BORDER SHORTCUTS
		if b_held and (keys[pygame.K_0] or keys[pygame.K_RIGHTBRACKET] or keys[pygame.K_LEFTBRACKET]):
			if not border_switch:
				border_switch = True
				if keys[pygame.K_0]: # default border
					new_background.border_size = Background.DEFAULT_BORDER
				elif keys[pygame.K_RIGHTBRACKET]: # max frame size
					new_background.border_size = Background.MAX_BORDER_SIZE
				elif keys[pygame.K_LEFTBRACKET]: # min frame size
					new_background.border_size = Background.MIN_BORDER_SIZE
		else:
			border_switch = False

		# REISIZE BORDERS
		border_dir = 0
		if b_held:
			if keys[pygame.K_EQUALS]:
				border_dir = 1
			elif keys[pygame.K_MINUS]:
				border_dir = -1
		new_background.resize_frame(border_dir)

		# TOGGLE ADAPTIVE BORDERS
		if ctrl_held and b_held:
			if not b_switch:
				b_switch = True
				# copies maze lines if not adaptive, otherwise sets adaptive color
				new_background.toggle_adaptive_frame()
				new_background.color_frame(new_maze.line_color)
		else:
			b_switch = False

		# ZOOM SHORTCUTS
		if ctrl_held and (keys[pygame.K_0] or keys[pygame.K_RIGHTBRACKET] or keys[pygame.K_LEFTBRACKET]):
			if not zoom_switch:
				zoom_switch = True
				if keys[pygame.K_0]: # default zoom
					new_maze.set_zoom(Maze.START_ZOOM)
				elif keys[pygame.K_RIGHTBRACKET]: # max zoom
					new_maze.set_zoom(0)
				elif keys[pygame.K_LEFTBRACKET]: # min zoom
					new_maze.set_zoom(1)
		else:
			zoom_switch = False

		# ZOOM IN/OUT
		m = 0
		if ctrl_held:
			# find direction
			if keys[pygame.K_EQUALS]: # plus
				m = 1
			elif keys[pygame.K_MINUS]: # minus
				m = -1
		new_maze.zoom(m) # zoom

		# PLAY MODE
		if playing:
			# SET SPEED
			alt_speed_btn = False # button for alt speed is pressed
			if not (caps_lock and shift_held):
				if caps_lock or shift_held: # on or the other
					alt_speed_btn = True
			# update speed only if its a new value
			if alt_speed_btn and not new_player.alt_speed: # change to alt
				new_player.set_speed(fps, new_player.ms_2)
				new_player.alt_speed = True
			elif not alt_speed_btn and new_player.alt_speed: # change to regular
				new_player.set_speed(fps, new_player.ms_1)
				new_player.alt_speed = False

			# SIZE SHORTCUTS
			if alt_held and (keys[pygame.K_0] or keys[pygame.K_RIGHTBRACKET] or keys[pygame.K_LEFTBRACKET]):
				if not player_size_switch:
					player_size_switch = True
					if keys[pygame.K_0]:
						new_player.update_size(Player.DEFAULT_SIZE)
					elif keys[pygame.K_RIGHTBRACKET]:
						new_player.update_size(Player.MAX_SIZE)
					elif keys[pygame.K_LEFTBRACKET]:
						new_player.update_size(Player.MIN_SIZE)
			else:
				player_size_switch = False

			# GROW
			if alt_held and keys[pygame.K_EQUALS]:
				new_player.grow(1)
			elif alt_held and keys[pygame.K_MINUS]:
				new_player.grow(-1) # shrink
			else:
				new_player.grow(0) # do not grow (must tick counter)

			# MOVE PLAYER
			move_dir = [0,0] # (y,x)
			move_pressed = False
			if keys[pygame.K_UP]:
				move_dir[0] -= 1
				move_pressed = True
			if keys[pygame.K_DOWN]:
				move_dir[0] += 1
				move_pressed = True
			if keys[pygame.K_LEFT]:
				move_dir[1] -= 1
				move_pressed = True
			if keys[pygame.K_RIGHT]:
				move_dir[1] += 1
				move_pressed = True
			if not move_pressed: # released
				new_player.cont_movement = False # kill momentum
				if new_player.manual_override:
					new_player.move_counter = 0 # startup immediately
			new_player.move(move_dir, new_maze.data) # move to new cell (if possible)
			new_player.check_escaped(new_maze.finish_cell)
			new_maze.set_frame_center(new_player.cell) # center window around player

			# TELEPORT
			if keys[pygame.K_1]: # home
				if not one_switch:
					one_switch = True
					new_player.set_pos(new_maze.start_cell)
			else:
				one_switch = False

			if keys[pygame.K_2]: # finish
				if not two_switch:
					two_switch = True
					if new_player.escaped:
						new_player.set_pos(new_maze.finish_cell)
			else:
				two_switch = False

			if keys[pygame.K_3]: # random location
				if not three_switch:
					three_switch = True
					if new_player.escaped:
						new_player.set_pos(new_maze.random_location())
			else:
				three_switch = False

		# VIEW MODE
		else:
			# SCROLL -- [row, column]
			scroll_dir = [0,0]
			if keys[pygame.K_LEFT]: # SCROLL LEFT
				scroll_dir[1] -= 1
			if keys[pygame.K_RIGHT]: # SCROLL RIGHT
				scroll_dir[1] += 1
			if keys[pygame.K_UP]: # SCROLL UP
				scroll_dir[0] -= 1
			if keys[pygame.K_DOWN]: # SCROLL DOWN
				scroll_dir[0] += 1
			new_maze.scroll(scroll_dir)

			# FRAME SHORTCUTS
			if keys[pygame.K_1]:
				new_maze.set_frame_quadrant(1)
			elif keys[pygame.K_2]:
				new_maze.set_frame_quadrant(2)
			elif keys[pygame.K_3]:
				new_maze.set_frame_quadrant(3)
			elif keys[pygame.K_4]:
				new_maze.set_frame_quadrant(4)
			elif keys[pygame.K_5]: # middle
				new_maze.set_frame_center((new_maze.rows/2,new_maze.cols/2))

		# EVENTS
		for event in pygame.event.get():
			if event.type == pygame.QUIT:
				active = False # end
			# MOUSE WHEEL EVENT
			elif event.type == pygame.MOUSEWHEEL:
				# ZOOM MAZE -- by 1 row/col
				if ctrl_held:
					new_maze.zoom(event.y)
				# LINE SIZE
				elif v_held:
					new_maze.expand_lines(event.y)
				# BORDER SIZE
				elif b_held:
					new_background.resize_frame(Background.STEP_SIZE * event.y)
				# ZOOM PLAYER
				elif playing and alt_held:
					new_player.grow(event.y)
				# PAN
				elif not playing:
					if shift_held:
						new_maze.scroll([event.x, -event.y]) # horizontal
					else:
						new_maze.scroll([-event.y, event.x]) # vertical

		# UPDATE DISPLAY
		# ----- background screen -----
		screen.fill(new_background.color)
		# ----- maze -----
		new_maze.fill()
		new_maze.draw_exits()
		if playing:
			new_player.draw(new_maze)
		new_maze.draw_borders()
		new_maze.draw_board(screen, new_background.border_size, new_background.frame_color) # outside border around maze
		screen.blit(new_maze.surface, new_maze.win_pos) # add maze to screen
		# ----- refresh -----
		pygame.display.update() # draw to screen
		clock.tick(fps)
	return

random.seed(time.time()) # generate random seed
main()
pygame.quit()