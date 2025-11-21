"""
Author:    Suriya Chellappan
Completed: 2025-11-21
Made for solving the Jane Street Puzzle, Nov 2025

This version:
- Uses the same logic as the original program.
- Saves:
    * all good grids into one file: good_grids.txt
    * all good meshes into one file: good_meshes.txt
- Prints only high-level progress and prints each good grid and each good mesh.
"""

'''
Things to consider:
-Arrow tiles are never box tiles
-Number tiles are always box tiles
-Tiles directly orthogonal to arrows that the arrow does not face are never box tiles
-Arrows can point to a tile past another arrow
-Number tiles within a row or column of an arrow give the upper bound on how far that arrow can point
-"Squeeze Theorem": arrows that point toward each other always have their closest box tile in between them,
 which also creates an upper bound
-Arrows pointing from different axes do not necessarily point to the same tile nor are the tiles necessarily closer than the
 intersecting tile
-Invalid tiles (never-box-tiles) may create a lower bound if orthogonal an arrow pointed at it, and can even create a bigger
 lower bound by chaining more invalid tiles in that direction
-Boundary is also the upper bound
-If number=#tiles valid, then all valid tiles are box tiles
-Numbers include their own cell + kings move
-Invalid can be determined by arrows and their lower bound
-Make arrows in binary: 0000=urbl (up, right, down, left), so 0 is no arrow and 1111=16 is arrow in every direction
-Base off of tile in the corner of the box (say, lower-bottom-left), and have the dimensions of the box (in the right
 order), then it folds only one possible way
-Number of box tiles has to factor into 2 and after that is a sum of 3 rectangular numbers (which still could be anything since
 1 is included)

Elimination done, now folding consideration:
-False: It is possible that all the uncertain tiles can be ignored for a check of using circles and squares to pick a corner & dimensions,
 then either they line up or they don't, so we can eliminate many corner/dimensions in that way
-Unknown: dimensions, corners, 0s on main grid
-Consider the minimum viable path; going thru minimum number of 0s to use as connecting paths, then maybe brute forcing to check
 for any overlaps, unpluggable holes, misaligned squares or circles that are inevitable on any folding
-...or at least which 0s can totally be avoided (before a full check, not that they are necessarily invalid) like spurs
-Find any paths that connect circles and/or squares first
-Remember that even 1 flip to certain can change a lot, as it anchors arrows which may even start a chain reaction with
 anchoring other arrows
-Go thru all possible paths before folding consideration? Might be a bit strenuous, even with chain reactions, although
 maybe there is another way to eliminate, like num tiles being specific "magic" numbers
 -Limit for a dimension is... 18

Method:
-Main grid should have a baseline for invalid/valid/certain tiles for being box tiles
-Other "arrow" grid keeping track of upper and lower bounds (or just store them as lists of x,y,lower,upper);
 store pointers
-Grid or list or some other way to track numbers with their constrictions as well

-For each arrow, find upper/lower bounds based on closest number in row/column, then squeeze/main grid boundary
 (remember to offset bounds based on if number is in the pointed direction or not)
-Mark all < lower bounds as invalid (including self), then also = lower bounds as invalid iff not in pointed direction
-Check each number to see if # valid tiles = number, and turn into certain tiles if so (if < number, throw an error)
-Repeat process
'''

from copy import deepcopy as dc

# From validCounts()
dims = {
    134: [[1, 3, 16]],
    138: [[1, 4, 13], [1, 6, 9], [3, 3, 10]],
    136: [[2, 2, 16], [2, 4, 10], [2, 6, 7], [3, 4, 8]],
    132: [[2, 3, 12], [2, 5, 8]]
}


class Arrow:
    def __init__(self, row, col, direction, lower=1, upper=19):
        self.r = row
        self.c = col
        self.dr = direction
        self.lower = lower
        self.upper = upper
        
        self.left = self.dr & 1 == 1
        self.down = (self.dr >> 1) & 1 == 1
        self.right = (self.dr >> 2) & 1 == 1
        self.up = (self.dr >> 3) & 1 == 1
        
        self.completed = False
    
    def SetAsComplete(self):
        self.completed = True
    
    def GetRowCol(self):
        return self.r, self.c
    
    def RestrictRangeFromNum(self, numInGrid):
        r2, c2, n = numInGrid
        if r2 != self.r and c2 != self.c:
            return
        dv = [r2-self.r, c2-self.c]
        d = dv[0]+dv[1]
        isPointingHere = self.IsPointingHere(dv)
        
        newMax = abs(d)
        if not isPointingHere:
            newMax -= 1
        
        if newMax < self.upper:
            self.upper = newMax
    
    def RestrictRangeFromBoundary(self):
        m1, m2, m3, m4 = [self.upper]*4
        if self.up:
            m1 = self.r
        if self.right:
            m2 = 19 - self.c
        if self.down:
            m3 = 19 - self.r
        if self.left:
            m4 = self.c
        
        self.upper = min(m1, m2, m3, m4)
        
    def IsPointingHere(self, displacement):
        dr, dc = displacement
        if self.up and dr < 0 and dc == 0:
            return True
        if self.right and dr == 0 and dc > 0:
            return True
        if self.down and dr > 0 and dc == 0:
            return True
        if self.left and dr == 0 and dc < 0:
            return True
        
        return False
        

class Grid:
    def __init__(self, setup=True):
        self.mainGrid = [[0] * 20 for _ in range(20)] # -1 invalid, 1 certain, 0 undetermined
        self.arrowPointerGrid = [[-1] * 20 for _ in range(20)]
        self.numsInGrid = [[-1] * 20 for _ in range(20)]
        
        self.countMin = 0
        self.countMax = 400
        
        self.invalidGrid = False
        
        # Each arrow: [r, c, dir (binary: urdl), lower, upper]
        self.arrows = [
            Arrow( 0, 1,0b0100,1,19),
            Arrow( 0, 8,0b0011,1,19),
            Arrow( 0,12,0b0010,1,19),
            Arrow( 0,15,0b0010,1,19),
            Arrow( 0,19,0b0011,1,19),
            Arrow( 1, 4,0b0100,1,19),
            Arrow( 1,13,0b0111,1,19),
            Arrow( 2, 6,0b0100,1,19),
            Arrow( 2, 9,0b0111,1,19),
            Arrow( 2,18,0b1011,1,19),
            Arrow( 3, 1,0b0010,1,19),
            Arrow( 3, 3,0b0110,1,19),
            Arrow( 4, 0,0b0100,1,19),
            Arrow( 4, 5,0b0110,1,19),
            Arrow( 4,15,0b1101,1,19),
            Arrow( 5,11,0b0110,1,19),
            Arrow( 6, 3,0b0010,1,19),
            Arrow( 6,10,0b0101,1,19),
            Arrow( 6,13,0b1011,1,19),
            Arrow( 6,16,0b0100,1,19),
            Arrow( 6,19,0b0011,1,19),
            Arrow( 7, 1,0b0110,1,19),
            Arrow( 7,14,0b0011,1,19),
            Arrow( 8, 5,0b1110,1,19),
            Arrow( 8, 9,0b1111,1,19),
            Arrow( 9, 1,0b1100,1,19),
            Arrow( 9,12,0b1101,1,19),
            Arrow( 9,16,0b0110,1,19),
            Arrow( 9,18,0b1011,1,19),
            Arrow(10, 1,0b1000,1,19),
            Arrow(10, 3,0b1010,1,19),
            Arrow(11, 8,0b1101,1,19),
            Arrow(11,10,0b0101,1,19),
            Arrow(11,14,0b1101,1,19),
            Arrow(11,17,0b1001,1,19),
            Arrow(12, 2,0b1100,1,19),
            Arrow(12, 5,0b1111,1,19),
            Arrow(12,18,0b1000,1,19),
            Arrow(13, 0,0b0100,1,19),
            Arrow(13,12,0b1001,1,19),
            Arrow(13,16,0b1000,1,19),
            Arrow(14, 8,0b1011,1,19),
            Arrow(14,11,0b1010,1,19),
            Arrow(14,13,0b0010,1,19),
            Arrow(15, 2,0b1100,1,19),
            Arrow(15, 4,0b1000,1,19),
            Arrow(15, 9,0b0011,1,19),
            Arrow(15,14,0b0011,1,19),
            Arrow(15,19,0b0001,1,19),
            Arrow(16, 5,0b1000,1,19),
            Arrow(16, 7,0b1100,1,19),
            Arrow(16,16,0b0001,1,19),
            Arrow(16,18,0b1001,1,19),
            Arrow(17, 1,0b0100,1,19),
            Arrow(17,10,0b1011,1,19),
            Arrow(18, 4,0b1100,1,19),
            Arrow(18, 6,0b0100,1,19),
            Arrow(18,14,0b1001,1,19),
            Arrow(19, 0,0b0100,1,19),
            Arrow(19, 4,0b1100,1,19),
            Arrow(19, 7,0b0100,1,19),
            Arrow(19,11,0b0001,1,19),
            Arrow(19,18,0b1001,1,19)
        ]
        
        # [row, col, num]
        self.numsInGridList = [
            [ 1,11, 4],
            [ 1,15, 4],
            [ 2, 7, 5],
            [ 3,12, 7],
            [ 3,14, 5],
            [ 4,10, 4],
            [ 4,13, 7],
            [ 4,17, 4],
            [ 5, 6, 4],
            [ 5, 8, 7],
            [ 6, 7, 9],
            [ 7,17, 6],
            [ 8, 2, 7],
            [ 8,11, 5],
            [ 9,14, 5],
            [10, 5, 4],
            [10, 7, 7],
            [10,18, 3],
            [13, 3, 5],
            [13, 6, 6],
            [13, 9, 2],
            [15, 6, 5],
            [17,12, 5],
            [17,13, 5],
            [18, 8, 4]
        ]
        
        self.circleTiles = [
            [1, 15],
            [3, 14],
            [4, 10],
            [4, 17],
            [8, 2],
            [17, 12]
        ]
        self.squareTiles = [
            [2, 7],
            [5, 8],
            [7, 17],
            [8, 11],
            [10, 18],
            [13, 3],
            [18, 8]
        ]
        
        self.showErrors = False
        
        if setup:
            for i, arrow in enumerate(self.arrows):
                r, c = arrow.GetRowCol()
                self.arrowPointerGrid[r][c] = i
            
            for numInCell in self.numsInGridList:
                r, c, n = numInCell[0], numInCell[1], numInCell[2]
                self.numsInGrid[r][c] = n
            
            # manually found constraints
            self.setMainGrid(8, 6, 1)
            self.setMainGrid(1, 7, 1)
            self.setMainGrid(10, 13, -1)
            self.setMainGrid(8, 14, 1)
            self.setMainGrid(11, 4, -1)
            self.setMainGrid(9, 10, -1)
            
            print("Initial grid setup complete. Running FindInitBaseGrid...")
            self.FindInitBaseGrid()
            self.mainGridCounts()
    
    def GetNum(self, r, c):
        for numTile in self.numsInGridList:
            r2, c2, n = numTile
            if r == r2 and c == c2:
                return n
        return 0
    
    def compareGrid(self, otherGrid):
        for r in range(20):
            for c in range(20):
                vThis = self.getMainGridTile(r, c)
                vThat = otherGrid.getMainGridTile(r, c)
                if vThis != vThat:
                    return False
        return True
    
    def setGridAsInvalid(self):
        self.invalidGrid = True
    
    def mainGridCounts(self, prnt = True):
        counts = [0, 0, 0]
        for r in range(20):
            for c in range(20):
                val = self.getMainGridTile(r, c)
                counts[val+1] += 1
        
        cN1, c0, c1 = counts
        self.countMin = c1
        self.countMax = c0 + c1
        if prnt:
            print(f"Counts on box: invalid: {cN1}, valid range: {self.countMin}-{self.countMax}, unknown: {c0}")
        
        return {-1: cN1, 0: c0, 1: c1}
    
    def printGrid(self, grid=None, label=""):
        if grid is None:
            grid = self.mainGrid
        s = "\n"
        if label:
            s += f"{label}\n"
        for r in range(len(grid)):
            s += "["
            for c in range(len(grid[0])):
                if c > 0:
                    s += ","
                val = grid[r][c]
                if val == 1:
                    s += "  1"
                elif val == 0:
                    s += "  ."
                elif val == -1:
                    s += "XXX"
                else:
                    s += "  " + str(val)
            s += "]\n"
        print(s)
        
    def getArrow(self, row, col):
        arrowIndex = self.arrowPointerGrid[row][col]
        if arrowIndex == -1:
            return None
        
        arrow = self.arrows[arrowIndex]
        return arrow
    
    def setMainGrid(self, row, col, val):
        if row < 0 or row > 19 or col < 0 or col > 19:
            return
        if val*-1 == self.getMainGridTile(row, col) and abs(val) > 0:
            if self.showErrors:
                print("ERROR, OVERWRITING VALIDITY THAT WAS ALREADY DETERMINED!")
            self.setGridAsInvalid()
            
        if self.getMainGridTile(row, col) != val:
            self.changeInLoop = True
        
        self.mainGrid[row][col] = val
    
    def getMainGridTile(self, row, col):
        if row < 0 or row > 19 or col < 0 or col > 19:
            return -2
        return self.mainGrid[row][col]
        
    def FindInitBaseGrid(self):
        # number tiles are in box
        for numInCell in self.numsInGridList:
            r, c, n = numInCell
            self.setMainGrid(r, c, 1)
        # arrow tiles (and orthogonal non-pointed) are out
        for arrow in self.arrows:
            r, c = arrow.GetRowCol()
            self.setMainGrid(r, c, -1)
            if not arrow.up:
                self.setMainGrid(r-1, c, -1)
            if not arrow.right:
                self.setMainGrid(r, c+1, -1)
            if not arrow.down:
                self.setMainGrid(r+1, c, -1)
            if not arrow.left:
                self.setMainGrid(r, c-1, -1)
        
        # restrict arrow range from numbers
        for arrow in self.arrows:
            for numInCell in self.numsInGridList:
                arrow.RestrictRangeFromNum(numInCell)
        
        # boundary
        for arrow in self.arrows:
            arrow.RestrictRangeFromBoundary()
        
        # squeeze pairs of arrows
        for arrow in self.arrows:
            for arrow2 in self.arrows:
                if arrow is arrow2:
                    continue
                dv1 = [arrow2.r-arrow.r, arrow2.c-arrow.c]
                dv2 = [arrow.r-arrow2.r, arrow.c-arrow2.c]
                p1 = arrow.IsPointingHere(dv1)
                p2 = arrow2.IsPointingHere(dv2)
                if p1 and p2:
                    dist = abs(dv1[0] + dv1[1])
                    newMax = dist - 1
                    arrow.upper = min(arrow.upper, newMax)
                    arrow2.upper = min(arrow2.upper, newMax)
        
        self.RepeatGridRestriction()
    
    def RepeatGridRestriction(self):
        print("  RepeatGridRestriction: starting logic iterations...")
        self.changeInLoop = True
        while self.changeInLoop:
            self.changeInLoop = False
            
            self.RestrictArrowRangeFromInvalidTiles()
            self.ArrowGuaranteedTiles()
            if self.invalidGrid:
                return False
            
            self.LockNumCertainTiles()
            if self.invalidGrid:
                return False
            
            self.MazeCheck()
            if self.invalidGrid:
                return False
            
            self.MazeBlockingCheck()
            self.RestrictArrowRangeFromConfirmedTiles()
        print("  RepeatGridRestriction: reached fixed point.")
        return True
    
    def RestrictArrowRangeFromInvalidTiles(self):
        while True:
            change = False
            for arrow in self.arrows:
                r, c = arrow.GetRowCol()
                minTiles = []
                maxTiles = []
                minim = arrow.lower
                maxim = arrow.upper
                arrowDirs = []
                if arrow.up:
                    minTiles.append([r - minim, c])
                    maxTiles.append([r - maxim, c])
                    arrowDirs.append([-1, 0])
                if arrow.right:
                    minTiles.append([r, c + minim])
                    maxTiles.append([r, c + maxim])
                    arrowDirs.append([0, 1])
                if arrow.down:
                    minTiles.append([r + minim, c])
                    maxTiles.append([r + maxim, c])
                    arrowDirs.append([1, 0])
                if arrow.left:
                    minTiles.append([r, c - minim])
                    maxTiles.append([r, c - maxim])
                    arrowDirs.append([0, -1])
                
                # Restrict upper
                while True:
                    restrict = False
                    for tile in maxTiles:
                        r2, c2 = tile
                        if self.getMainGridTile(r2, c2) == -1:
                            restrict = True
                            change = True
                            self.changeInLoop = True
                            break
                    if not restrict:
                        break
                    
                    for j, tile in enumerate(maxTiles):
                        maxTiles[j] = [tile[0] - arrowDirs[j][0], tile[1] - arrowDirs[j][1]]
                    
                    arrow.upper -= 1
                
                # Restrict lower
                while True:
                    restrict = False
                    for tile in minTiles:
                        r2, c2 = tile
                        if self.getMainGridTile(r2, c2) == -1:
                            restrict = True
                            change = True
                            self.changeInLoop = True
                            break
                    if not restrict:
                        break
                    
                    for j, tile in enumerate(minTiles):
                        r2, c2 = tile
                        self.setMainGrid(r2, c2, -1)
                        minTiles[j] = [tile[0] + arrowDirs[j][0], tile[1] + arrowDirs[j][1]]
                    
                    arrow.lower += 1
                    minim += 1
                    
                    if not arrow.up:
                        self.setMainGrid(r - minim, c, -1)
                    if not arrow.right:
                        self.setMainGrid(r, c + minim, -1)
                    if not arrow.down:
                        self.setMainGrid(r + minim, c, -1)
                    if not arrow.left:
                        self.setMainGrid(r, c - minim, -1)
            
            if not change:
                break
    
    def ArrowGuaranteedTiles(self):
        for i, arrow in enumerate(self.arrows):
            if arrow.upper < arrow.lower:
                if self.showErrors:
                    print(f"ERROR: no range for arrow {i} at [{arrow.r},{arrow.c}]")
                self.setGridAsInvalid()
                return
            if arrow.upper == arrow.lower and not arrow.completed:
                arrow.SetAsComplete()
                d = arrow.upper
                r, c = arrow.GetRowCol()
                if arrow.up:
                    self.setMainGrid(r - d, c, 1)
                if arrow.right:
                    self.setMainGrid(r, c + d, 1)
                if arrow.down:
                    self.setMainGrid(r + d, c, 1)
                if arrow.left:
                    self.setMainGrid(r, c - d, 1)
                    
    def LockNumCertainTiles(self):
        disps = [[dr,dc] for dr in range(-1,2) for dc in range(-1,2)]
        for numInCell in self.numsInGridList:
            r, c, n = numInCell
            count = 0
            count2 = 0
            validCheckTiles = []
            uncCheckTiles = []
            for disp in disps:
                r2, c2 = r+disp[0], c+disp[1]
                val = self.getMainGridTile(r2, c2)
                if val >= 0:
                    validCheckTiles.append([r2,c2])
                    count += 1
                    if val == 0:
                        uncCheckTiles.append([r2,c2])
                    if val == 1:
                        count2 += 1
            
            if count < n:
                if self.showErrors:
                    print(f"ERROR: not enough tiles near number {n} at [{r},{c}] (have {count})")
                self.setGridAsInvalid()
                return
            elif count == n:
                for r2, c2 in validCheckTiles:
                    self.setMainGrid(r2, c2, 1)
            elif count2 == n:
                for r2, c2 in uncCheckTiles:
                    self.setMainGrid(r2, c2, -1)
                
                    
    def MazeCheck(self, blockTile = (0, 0)): # [0,0] is already invalid, default no effect
        mazeGrid = [[0] * 20 for _ in range(20)]  # -1 wall, 0 untouched, 1 reached
        for r in range(20):
            for c in range(20):
                if self.getMainGridTile(r, c) == -1:
                    mazeGrid[r][c] = -1
        
        sr, sc = 2, 7 # a numbered tile to start
        mazeGrid[sr][sc] = 1
        blockR, blockC = blockTile
        mazeGrid[blockR][blockC] = -1
        
        oldTiles = [[sr, sc]]
        orthoDirs = [[-1, 0], [0, 1], [1, 0], [0, -1]]
        while True:
            newTiles = []
            for oldTile in oldTiles:
                for odir in orthoDirs:
                    ptr, ptc = oldTile[0]+odir[0], oldTile[1]+odir[1]
                    if 0 <= ptr < 20 and 0 <= ptc < 20 and mazeGrid[ptr][ptc] == 0:
                        mazeGrid[ptr][ptc] = 1
                        newTiles.append([ptr,ptc])
            if len(newTiles) == 0:
                break
            oldTiles = newTiles
        
        for r in range(20):
            for c in range(20):
                mainGridVal = self.getMainGridTile(r, c)
                mazeGridVal = mazeGrid[r][c]
                
                if mazeGridVal == 0:
                    if blockTile == (0, 0): # base maze
                        if mainGridVal == 1:
                            if self.showErrors:
                                print(f"ERROR: confirmed tile [{r},{c}] disconnected")
                            self.setGridAsInvalid()
                            return
                        self.setMainGrid(r, c, -1)
                    else: # block check maze
                        if mainGridVal == 1:
                            return False
        
        return True
    
    def MazeBlockingCheck(self):
        for r in range(20):
            for c in range(20):
                if self.getMainGridTile(r, c) == 0:
                    mazeBlockCheck = self.MazeCheck((r,c))
                    if mazeBlockCheck is False:
                        self.setMainGrid(r, c, 1)
                        
    def RestrictArrowRangeFromConfirmedTiles(self):
        orthoDirs = [[-1, 0], [0, 1], [1, 0], [0, -1]]
        for arrow in self.arrows:
            checkTiles = []
            moveDirs = []
            if arrow.up:
                checkTiles.append([arrow.r-arrow.lower, arrow.c])
                moveDirs.append(orthoDirs[0])
            if arrow.right:
                checkTiles.append([arrow.r, arrow.c+arrow.lower])
                moveDirs.append(orthoDirs[1])
            if arrow.down:
                checkTiles.append([arrow.r+arrow.lower, arrow.c])
                moveDirs.append(orthoDirs[2])
            if arrow.left:
                checkTiles.append([arrow.r, arrow.c-arrow.lower])
                moveDirs.append(orthoDirs[3])
            
            def discoveryLoop(arrow):
                for dist in range(arrow.lower, arrow.upper):
                    for j, checkTile in enumerate(checkTiles):
                        r,c = checkTile
                        if self.getMainGridTile(r, c) == 1:
                            arrow.upper = dist
                            self.changeInLoop = True
                            return
                        checkTiles[j] = [checkTile[0] + moveDirs[j][0], checkTile[1] + moveDirs[j][1]]
            
            discoveryLoop(arrow)
            
    
    def DeadMazeCheck(self):
        # check for internal air pockets (holes)
        mazeGrid = [[0] * 22 for _ in range(22)]  # -1 wall, 0 untouched, 1 reached
        for r in range(20):
            for c in range(20):
                if self.getMainGridTile(r, c) != -1:
                    mazeGrid[r+1][c+1] = -1
        
        sr, sc = 0, 0
        mazeGrid[sr][sc] = 1
        
        oldTiles = [[sr, sc]]
        orthoDirs = [[-1, 0], [0, 1], [1, 0], [0, -1]]
        while True:
            newTiles = []
            for oldTile in oldTiles:
                for odir in orthoDirs:
                    ptr, ptc = oldTile[0] + odir[0], oldTile[1] + odir[1]
                    if 0 <= ptr < 22 and 0 <= ptc < 22 and mazeGrid[ptr][ptc] == 0:
                        mazeGrid[ptr][ptc] = 1
                        newTiles.append([ptr,ptc])
            if len(newTiles) == 0:
                break
            oldTiles = newTiles
        
        for r in range(1, 21):
            for c in range(1, 21):
                if mazeGrid[r][c] == 0:
                    return False
        return True
    

class MeshGrid:
    def __init__(self, nRows, nCols, nLayers, sr, sc, gridI):
        self.nr = nRows
        self.nc = nCols
        self.nl = nLayers
        
        self.sr = sr
        self.sc = sc
        self.gridI = gridI
        
        self.frontGrid = [[0] * self.nc for _ in range(self.nr)]
        self.backGrid = [[0] * self.nc for _ in range(self.nr)]
        self.topGrid = [[0] * self.nc for _ in range(self.nl)]
        self.botGrid = [[0] * self.nc for _ in range(self.nl)]
        self.leftGrid = [[0] * self.nl for _ in range(self.nr)]
        self.rightGrid = [[0] * self.nl for _ in range(self.nr)]
        
        self.circles = []
        self.squares = []
        
        self.sideToGrid = {
            "front": self.frontGrid, "back": self.backGrid, "top": self.topGrid,
            "bot": self.botGrid, "left": self.leftGrid, "right": self.rightGrid
        }
        
        self.sideToPlaceFunc = {
            "front": self.PlaceOnFrontGrid, "back": self.PlaceOnBackGrid,
            "top": self.PlaceOnTopGrid, "bot": self.PlaceOnBotGrid,
            "left": self.PlaceOnLeftGrid, "right": self.PlaceOnRightGrid
        }
        
        self.nums = [0, 0, 0, 0, 0, 0]
        self.currentN = 0
    
    def PrintMeshGrid(self):
        print(f"\nMesh from grid #{self.gridI}")
        print(f"Dimensions: [{self.nr}, {self.nc}, {self.nl}]")
        self.PrintFace("front")
        self.PrintFace("top")
        self.PrintFace("back")
        self.PrintFace("bot")
        self.PrintFace("left")
        self.PrintFace("right")
    
    def PrintFace(self, face):
        faceGrid = self.sideToGrid[face]
        s = f"{face}:\n"
        for r in range(len(faceGrid)):
            s += "["
            for c in range(len(faceGrid[0])):
                if c > 0:
                    s += ","
                val = faceGrid[r][c]
                if val == 1:
                    s += "  1"
                elif val == 2:
                    s += "op2"
                elif val == 3:
                    s += "sq3"
                else:
                    s += "  ."
            s += "]\n"
        print(s)
    
    def Place(self, side, r, c, t, o, n):
        self.currentN = n
        return self.sideToPlaceFunc[side](r, c, t, o)
    
    def PlaceType(self, side, r, c, t):
        if t == 2:
            self.circles.append([side, r, c])
        if t == 3:
            self.squares.append([side, r, c])
    
    def PlaceOnFrontGrid(self, r, c, t, o):
        if r == -1:
            return self.PlaceOnTopGrid(self.nl - 1, c, t, o)
        if r == self.nr:
            return self.PlaceOnBotGrid(0, c, t, o)
        if c == -1:
            return self.PlaceOnLeftGrid(r, self.nl - 1, t, o)
        if c == self.nc:
            return self.PlaceOnRightGrid(r, 0, t, o)
        
        if self.frontGrid[r][c] > 0:
            return None
        
        self.nums[0] += self.currentN
        self.frontGrid[r][c] = t
        self.PlaceType("front", r, c, t)
        return ["front", r, c, o%4]
    
    def PlaceOnBackGrid(self, r, c, t, o):
        if r == -1:
            return self.PlaceOnBotGrid(self.nl - 1, c, t, o)
        if r == self.nr:
            return self.PlaceOnTopGrid(0, c, t, o)
        if c == -1:
            return self.PlaceOnLeftGrid(self.nr - r - 1, 0, t, o+2)
        if c == self.nc:
            return self.PlaceOnRightGrid(self.nr - r - 1, self.nl - 1, t, o+2)
        
        if self.backGrid[r][c] > 0:
            return None
        
        self.nums[1] += self.currentN
        self.backGrid[r][c] = t
        self.PlaceType("back", r, c, t)
        return ["back", r, c, o%4]
    
    def PlaceOnTopGrid(self, r, c, t, o):
        if r == -1:
            return self.PlaceOnBackGrid(self.nr - 1, c, t, o)
        if r == self.nl:
            return self.PlaceOnFrontGrid(0, c, t, o)
        if c == -1:
            return self.PlaceOnLeftGrid(0, r, t, o-1)
        if c == self.nc:
            return self.PlaceOnRightGrid(0, self.nl - r - 1, t, o+1)
        
        if self.topGrid[r][c] > 0:
            return None
        
        self.nums[2] += self.currentN
        self.topGrid[r][c] = t
        self.PlaceType("top", r, c, t)
        return ["top", r, c, o%4]
    
    def PlaceOnBotGrid(self, r, c, t, o):
        if r == -1:
            return self.PlaceOnFrontGrid(self.nr - 1, c, t, o)
        if r == self.nl:
            return self.PlaceOnBackGrid(0, c, t, o)
        if c == -1:
            return self.PlaceOnLeftGrid(self.nr - 1, self.nl - r - 1, t, o+1)
        if c == self.nc:
            return self.PlaceOnRightGrid(self.nr - 1, r, t, o-1)
        
        if self.botGrid[r][c] > 0:
            return None
        
        self.nums[3] += self.currentN
        self.botGrid[r][c] = t
        self.PlaceType("bot", r, c, t)
        return ["bot", r, c, o%4]
    
    def PlaceOnLeftGrid(self, r, c, t, o):
        if r == -1:
            return self.PlaceOnTopGrid(c, 0, t, o+1)
        if r == self.nr:
            return self.PlaceOnBotGrid(self.nl - c - 1, 0, t, o-1)
        if c == -1:
            return self.PlaceOnBackGrid(self.nr - r - 1, 0, t, o+2)
        if c == self.nl:
            return self.PlaceOnFrontGrid(r, 0, t, o)
        
        if self.leftGrid[r][c] > 0:
            return None
        
        self.nums[4] += self.currentN
        self.leftGrid[r][c] = t
        self.PlaceType("left", r, c, t)
        return ["left", r, c, o%4]
    
    def PlaceOnRightGrid(self, r, c, t, o):
        if r == -1:
            return self.PlaceOnTopGrid(self.nl - c - 1, self.nc - 1, t, o-1)
        if r == self.nr:
            return self.PlaceOnBotGrid(c, self.nc - 1, t, o+1)
        if c == -1:
            return self.PlaceOnFrontGrid(r, self.nc - 1, t, o)
        if c == self.nl:
            return self.PlaceOnBackGrid(self.nr - r - 1, self.nc - 1, t, o+2)
        
        if self.rightGrid[r][c] > 0:
            return None
        
        self.nums[5] += self.currentN
        self.rightGrid[r][c] = t
        self.PlaceType("right", r, c, t)
        return ["right", r, c, o%4]
    
    
    def CheckCircles(self):
        for circle in self.circles:
            side, r, c = circle
            if side == "front":
                opposite = ["back", self.nr - r - 1, c]
            elif side == "top":
                opposite = ["bot", self.nr - r - 1, c]
            elif side == "left":
                opposite = ["right", r, self.nl - c - 1]
            else:
                continue
            if opposite not in self.circles:
                return False
        return True
    
    def CheckSquares(self):
        for square in self.squares:
            side, r, c = square
            grid = self.sideToGrid[side]
            nr, nc = len(grid), len(grid[0])
            checkTiles = [[r-1, c], [r+1, c], [r, c-1], [r, c+1]]
            goodTile = False
            for r2, c2 in checkTiles:
                if 0 <= r2 < nr and 0 <= c2 < nc:
                    if [side, r2, c2] in self.squares:
                        goodTile = True
                        break
            if not goodTile:
                return False
        return True
    
    def CalcAnswer(self):
        ans = 1
        for numSum in self.nums:
            ans *= numSum
        
        print(f"Face sums: {self.nums}")
        print(f"Final answer: {ans}")
        return ans


class ShutTheBox:
    def __init__(self):
        print("Step 1: Building initial grid and running base logic...")
        self.grid = Grid()
        self.grid.printGrid(label="Initial grid after base logic")
        self.grids = [self.grid]
        
        self.fullDims = {}
        
        self.goodGridsToCheck = []
        self.goodMeshes = []
        
    def MainProcess1(self):
        print("\n=== MainProcess1: Exploring possible 2D nets ===")
        oldCounts = self.grid.mainGridCounts()
        while True:
            newCounts = self.GridSplitBinaryTree()
            if oldCounts[0] == newCounts[0]:
                print("  GridSplitBinaryTree: unknown count unchanged, stopping iterations.")
                break
            oldCounts = newCounts
        
        print("  Final narrowing pass with split=True...")
        self.GridSplitBinaryTree(split=True)
        
        print("  Computing all possible 3D dimension permutations...")
        self.CalcFullDims()
        
        print("  Saving all good grids into good_grids.txt ...")
        self.SaveGoodGridsToFile()
        print("  Done saving good grids.")
    
    def CalcFullDims(self):
        self.fullDims = {}
        for nTiles in dims:
            newListForN = []
            dsListForN = dims[nTiles]
            for ds in dsListForN:
                d1, d2, d3 = ds
                newListForN += [[d1, d2, d3]]
                if d1 == d2 and d2 == d3:
                    continue
                newListForN += [[d2, d3, d1]]
                newListForN += [[d3, d1, d2]]
                if d2 != d3 and d1 != d2 and d1 != d3:
                    newListForN += [[d1, d3, d2]]
                    newListForN += [[d2, d1, d3]]
                    newListForN += [[d3, d2, d1]]
            
            self.fullDims[nTiles] = newListForN
        
        # For tests:
        self.fullDims[54] = [[3,3,3]]
        
        print("  Possible dimension sets:", self.fullDims)
        
    
    def GridSplitBinaryTree(self, split=False):
        print(f"  GridSplitBinaryTree pass (split={split})...")
        oldGrids = self.grids
        ogGrid = self.grid
        
        for r in range(20):
            for c in range(20):
                if ogGrid.getMainGridTile(r, c) != 0:
                    continue
                newGrids = []
                invalidReached = False
                for grid in oldGrids:
                    if grid.getMainGridTile(r, c) != 0:
                        newGrids.append(grid)
                        continue
                    for val in [-1, 1]:
                        newGrid = dc(grid)
                        newGrid.setMainGrid(r, c, val)
                        newGrid.RepeatGridRestriction()
                        
                        if not newGrid.invalidGrid:
                            newGrids.append(newGrid)
                        else:
                            invalidReached = True
                            
                if invalidReached or split:
                    oldGrids = newGrids
                    print(f"    Decided cell ({r},{c}); number of grids: {len(oldGrids)}")
                
        print(f"  Done with GridSplitBinaryTree; grids count after pass: {len(oldGrids)}")
        if split:
            # filter by possible tile counts
            removeGrids = []
            for g in oldGrids:
                count = g.mainGridCounts(prnt=False)
                if count[1] not in dims:
                    removeGrids.append(g)
            for g in removeGrids:
                oldGrids.remove(g)
            print(f"  After dimension filter: {len(oldGrids)} grids")
            
            # filter by no-holes condition
            removeGrids = []
            for g in oldGrids:
                if not g.DeadMazeCheck():
                    removeGrids.append(g)
            for g in removeGrids:
                oldGrids.remove(g)
            print(f"  After no-hole filter: {len(oldGrids)} grids")
            
            counts = []
            for i, g in enumerate(oldGrids):
                c = g.mainGridCounts(prnt=False)
                if c[1] not in counts:
                    counts.append(c[1])
                print(f"  Candidate grid #{i}:")
                g.printGrid()
            counts.sort()
            print(f"  FINAL possible tile counts: {counts}")
            
        self.grids = oldGrids
        if self.grids:
            counts = self.grids[0].mainGridCounts()
        else:
            counts = {-1: 0, 0: 0, 1: 0}
        return counts
    
    
    def SaveGoodGridsToFile(self, filename="good_grids.txt"):
        """Save all good candidate grids into one text file, appended one after another."""
        grids = self.goodGridsToCheck = self.grids
        with open(filename, "w") as file:
            for i, grid in enumerate(grids):
                file.write(f"Grid #{i}:\n")
                gridMeat = grid.mainGrid
                for r in range(len(gridMeat)):
                    for c in range(len(gridMeat[0])):
                        val = grid.getMainGridTile(r, c)
                        file.write(str(val+1))  # same encoding as your original file
                    file.write("\n")
                file.write("\n")
            file.write(f"End; num grids: {len(grids)}\n")
    
    def LoadGoodGridsFromFile(self, filename="good_grids.txt", prnt=False):
        self.goodGridsToCheck = []
        with open(filename, "r") as file:
            while True:
                line = file.readline()
                if not line:
                    break
                if line.startswith("Grid #"):
                    newGrid = Grid(setup=False)
                    for r in range(20):
                        line = file.readline().strip()
                        for c in range(20):
                            char = line[c]
                            val = int(char)-1
                            newGrid.setMainGrid(r, c, val)
                    self.goodGridsToCheck.append(newGrid)
                if line.startswith("End;"):
                    break
        
        if prnt:
            for i, grid in enumerate(self.goodGridsToCheck):
                print(f"Grid #{i}:")
                grid.printGrid()
                
    
    
    def BoxAGrid(self, grid, gridI, startTile=(19, 9)):
        print(f"\n  BoxAGrid: trying to fold grid #{gridI} into a 3D box...")
        nGoodMeshes = 0
        nTiles = grid.mainGridCounts(prnt=False)[1]
        possibleDims = self.fullDims.get(nTiles, [])
        print(f"    nTiles={nTiles}, possibleDims={possibleDims}")
        for ds in possibleDims:
            nr, nc, nl = ds
            for sr in range(nr):
                for sc in range(nc):
                    meshGrid = MeshGrid(nr, nc, nl, sr, sc, gridI)
                    meshGrid.PlaceOnFrontGrid(sr, sc, 1, 0)
                    mazeGrid = dc(grid.mainGrid)
                    
                    oldTilesMesh = [["front", sr, sc, 0]]
                    oldTilesFlat = [[startTile[0], startTile[1]]]
                    mazeGrid[startTile[0]][startTile[1]] = 2
                    badMesh = False
                    while True:
                        newTilesMesh = []
                        newTilesFlat = []
                        for i, oldTileMesh in enumerate(oldTilesMesh):
                            oldTileFlat = oldTilesFlat[i]
                            orthoDirs = [[-1, 0], [0, 1], [1, 0], [0, -1]]
                            for j, odir in enumerate(orthoDirs):
                                ptrF, ptcF = oldTileFlat[0] + odir[0], oldTileFlat[1] + odir[1]
                                if not (0 <= ptrF < 20 and 0 <= ptcF < 20):
                                    continue
                                if mazeGrid[ptrF][ptcF] != 1:
                                    continue
                                
                                n = grid.GetNum(ptrF, ptcF)

                                o = oldTileMesh[3]
                                odir2 = orthoDirs[(j+o)%4]
                                side, r0, c0, o0 = oldTileMesh
                                ptrM, ptcM = r0 + odir2[0], c0 + odir2[1]
                                
                                mazeGrid[ptrF][ptcF] = 2
                                
                                t = 1
                                baseTile = [ptrF, ptcF]
                                if baseTile in grid.circleTiles:
                                    t = 2
                                if baseTile in grid.squareTiles:
                                    t = 3
                                newTileMesh = meshGrid.Place(side, ptrM, ptcM, t, o0, n)
                                if newTileMesh is None:
                                    badMesh = True
                                    break
                                newTilesMesh.append(newTileMesh)
                                newTilesFlat.append([ptrF,ptcF])
                            if badMesh:
                                break

                        if len(newTilesMesh) == 0 or badMesh:
                            break
                        
                        oldTilesMesh = newTilesMesh
                        oldTilesFlat = newTilesFlat
                    
                    if badMesh:
                        continue
                        
                    if not meshGrid.CheckCircles():
                        continue
                    if not meshGrid.CheckSquares():
                        continue
                    
                    print("    Found a valid mesh for this grid!")
                    nGoodMeshes += 1
                    self.goodMeshes.append(meshGrid)
        
        print(f"  BoxAGrid: found {nGoodMeshes} good mesh(es) for grid #{gridI}")
    
    def BoxGrids(self):
        print("\n=== BoxGrids: Trying to fold each good 2D net into a 3D box ===")
        for i, grid in enumerate(self.goodGridsToCheck):
            print(f"Checking Grid #{i}")
            self.BoxAGrid(grid, i)
        
        print(f"\nTotal good meshes: {len(self.goodMeshes)}")
        for idx, goodMesh in enumerate(self.goodMeshes):
            print(f"\n=== Valid Mesh #{idx} (from grid #{goodMesh.gridI}) ===")
            goodMesh.PrintMeshGrid()
            print("  Corresponding 2D grid:")
            self.goodGridsToCheck[goodMesh.gridI].printGrid(label=f"Good grid #{goodMesh.gridI}")
            goodMesh.CalcAnswer()
        
        print("Saving all good meshes into good_meshes.txt ...")
        self.SaveAllMeshesToFile()
        print("Done saving good meshes.")
    
    def SaveAllMeshesToFile(self, filename="good_meshes.txt"):
        """Append all valid meshes into a single text file."""
        with open(filename, "w") as f:
            for idx, mesh in enumerate(self.goodMeshes):
                f.write(f"Mesh #{idx} from grid #{mesh.gridI}\n")
                f.write(f"Dimensions: {mesh.nr} x {mesh.nc} x {mesh.nl}\n\n")
                for faceName, faceGrid in [
                    ("front", mesh.frontGrid),
                    ("back", mesh.backGrid),
                    ("top", mesh.topGrid),
                    ("bot", mesh.botGrid),
                    ("left", mesh.leftGrid),
                    ("right", mesh.rightGrid),
                ]:
                    f.write(faceName + ":\n")
                    for row in faceGrid:
                        f.write(" ".join(str(v) for v in row) + "\n")
                    f.write("\n")
                f.write("Face sums: " + str(mesh.nums) + "\n")
                ans = 1
                for s in mesh.nums:
                    ans *= s
                f.write("Final answer: " + str(ans) + "\n\n")
    
    def MainProcess2(self):
        print("\n=== MainProcess2: Loading good grids and folding into boxes ===")
        self.CalcFullDims()
        self.LoadGoodGridsFromFile()
        self.BoxGrids()


def validCounts(mn, mx=None):
    if mx is None:
        mx = mn
    validDimensions = {}
    validNumbersOfTiles = []
    
    def nTilesBasedOnDim(d1, d2, d3):
        nTiles = 2 * (d1*d2 + d2*d3 + d1*d3)
        return nTiles
    
    for d1 in range(1, 100):
        c2 = 0
        for d2 in range(d1, 100):
            c3 = 0
            for d3 in range(d2, 19):
                n = nTilesBasedOnDim(d1, d2, d3)
                
                if n > mx:
                    break
                c2 += 1
                c3 += 1
                if n < mn:
                    continue

                dimensions = [d1, d2, d3]
                if n not in validNumbersOfTiles:
                    validNumbersOfTiles.append(n)
                    validDimensions[n] = [dimensions]
                else:
                    validDimensions[n] = validDimensions[n] + [dimensions]
            if c3 == 0:
                break
        if c2 == 0:
            break
    
    validNumbersOfTiles.sort()
    print(validNumbersOfTiles)
    print(len(validDimensions), validDimensions)


if __name__ == "__main__":
    # Step 1: generate all candidate 2D nets and save them
    stb = ShutTheBox()
    stb.MainProcess1()
    # Step 2: fold nets into 3D boxes, check circles/squares, compute answer
    stb.MainProcess2()

"""
Expected final output (for the correct box):

Face sums: [57, 28, 5, 11, 11, 17]
Final answer: 16414860
"""
