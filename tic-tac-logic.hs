import System.IO (isEOF)
import Debug.Trace
import Data.List

debug = flip trace

data Cell = E | X | O deriving (Eq,Show)

type Grid = [[Cell]]
type Pos = (Int,Int)

--- Print grid ---
makeString :: Cell -> String
makeString E = "."
makeString O = "O"
makeString X = "X"

makeRowGridString :: [Cell] -> String
makeRowGridString [] = []
makeRowGridString (x:xs) = makeString x ++ makeRowGridString xs

stringGrid :: Grid -> String
stringGrid [x] = makeRowGridString x
stringGrid (x:xs) = makeRowGridString x ++ "\n" ++ stringGrid xs

printGrid :: Grid -> IO()
printGrid grid = putStr (stringGrid grid ++ "\n")

--- End print grid ---

opposite :: Cell -> Cell
opposite X = O
opposite O = X
opposite _ = E

makeCell :: Char -> Cell
makeCell '.' = E
makeCell 'O' = O
makeCell 'X' = X

createGrid :: [String] -> Grid -> Grid
createGrid [] grid = grid
createGrid (x:xs) grid = createGrid xs (grid ++ [createGrid' x []])

createGrid' :: String -> [Cell] -> [Cell]
createGrid' [] grid = grid
createGrid' (s:str) grid = createGrid' str (grid ++ [makeCell s])

readLines :: [String] -> IO [String]
readLines grid = do
    end <- isEOF
    if end
        then return grid
        else do
            line <- getLine
            readLines (grid ++ [line])

getCell :: Grid -> Pos -> Cell
getCell grid (x,y) = grid!!x!!y

isEmpty :: Grid -> Pos -> Pos -> Bool
isEmpty grid pos gridsize = 
    if and [isValidPos pos gridsize, (getCell grid pos) == E]
    then True 
    else False

isValidPos :: Pos -> Pos -> Bool
isValidPos (x,y) (row,col) = and [x >= 0, x < row, y >= 0, y < col]

placeCell :: Grid -> Pos -> Cell -> Pos -> Grid
placeCell grid (x,y) cell gridsize =
    if and [isValidPos (x,y) gridsize, isEmpty grid (x,y) gridsize]
    then placeCell' grid x (placeCell' (grid!!x) y cell)
    else grid

placeCell' :: [a] -> Int -> a -> [a]
placeCell' grid i cell = take i grid ++ (cell: (drop (i+1) grid))

getCellPos :: Grid -> Cell -> Pos -> [Pos] -- Goes through whole grid
getCellPos grid cell (sizerow, sizecol) = concat [[(x,y) | y <- [0..(sizecol-1)], getCell grid (x,y) == cell] | x <- [0..(sizerow-1)]]

getCellRowPos :: Grid -> Cell -> Int -> Pos -> [Pos] -- Goes through given row
getCellRowPos grid cell xpos (_, sizecol) = concat [[(x, y) | y <- [0..(sizecol-1)], getCell grid (x, y) == cell] | x <- [xpos]]

countCell :: Grid -> Cell -> Pos -> Int
countCell grid cell gridsize = length (getCellPos grid cell gridsize)

-- from https://stackoverflow.com/questions/2097501/learning-haskell-how-to-remove-an-item-from-a-list-in-haskell
removePos :: Pos -> [Pos] -> [Pos]
removePos _ [] = []
removePos a (b:pos)
    | a == b = removePos a pos
    | otherwise = b : removePos a pos

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-----------------------         Basic Techniques         -----------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

-- Basic technique 1, avoid triples in pattern ".XX." and ".OO."
solveDouble :: Grid -> Pos -> Grid
solveDouble grid (sizerow, sizecol) = transpose (solveDoubleRow (solveDoubleRow (transpose (solveDoubleRow (solveDoubleRow grid O (sizerow, sizecol)) X (sizerow, sizecol))) O (sizecol, sizerow)) X (sizecol, sizerow))

solveDoubleRow :: Grid -> Cell -> Pos -> Grid
solveDoubleRow grid cell gridsize = solveDoubleRow' grid cell (getCellPos grid cell gridsize) gridsize

solveDoubleRow' :: Grid -> Cell -> [Pos] -> Pos -> Grid
solveDoubleRow' grid _ [] _ = grid
solveDoubleRow' grid cell ((x,y):pos) gridsize =
    if and [isValidPos (x,y+1) gridsize, getCell grid (x,y) == getCell grid (x, y+1)]
    then solveDoubleRow' (placeCell (placeCell grid (x, y-1) (opposite cell) gridsize) (x, y+2) (opposite cell) gridsize) cell (removePos (x,y+1) pos) gridsize
    else solveDoubleRow' grid cell pos gridsize

-- Basic technique 2, avoid triples in pattern "X.X" and "O.O".
solveInbetween :: Grid -> Pos -> Grid
solveInbetween grid (sizerow, sizecol) = transpose (solveInbetweenRow (solveInbetweenRow (transpose (solveInbetweenRow (solveInbetweenRow grid O (sizerow, sizecol)) X (sizerow, sizecol))) O (sizecol, sizerow)) X (sizecol, sizerow))

solveInbetweenRow :: Grid -> Cell -> Pos -> Grid
solveInbetweenRow grid cell gridsize = solveInbetweenRow' grid cell (getCellPos grid cell gridsize) gridsize

solveInbetweenRow' :: Grid -> Cell -> [Pos] -> Pos -> Grid
solveInbetweenRow' grid _ [] _ = grid
solveInbetweenRow' grid cell ((x,y):pos) gridsize =
    if and [isValidPos (x, y+2) gridsize, getCell grid (x,y+2) == getCell grid (x,y), isEmpty grid (x, y+1) gridsize]
    then solveInbetweenRow' (placeCell grid (x,y+1) (opposite cell) gridsize) cell pos gridsize
    else solveInbetweenRow' grid cell pos gridsize

solveForbidden grid (x,y) = 
    let gridRX = solveForbiddenRow grid X (x,y)
    in 
        let gridRO = solveForbiddenRow gridRX O (x,y)
        in 
            let gridCX = solveForbiddenRow (transpose gridRO) X (y,x)
            in 
                (transpose (solveForbiddenRow gridCX O (y,x)))

-- Basic technique 3, avoid forbidden triples in one or two steps later.
solveForbiddenRow :: Grid -> Cell -> Pos -> Grid
solveForbiddenRow grid cell gridsize = 
    solveForbiddenRow' grid gridsize cell 0 gridsize

solveForbiddenRow' :: Grid -> Pos -> Cell -> Int -> Pos -> Grid
solveForbiddenRow' grid gridsize cell counter (x,y) 
    | counter == x = grid
    | checkForForbiddenLine grid gridsize cell counter = 
        let emptys = getCellRowPos grid E counter (x,y) 
            wrongPositions = tryPlacements grid gridsize cell emptys 
        in placeOppositeCells grid (opposite cell) emptys wrongPositions (x,y)
    | otherwise = solveForbiddenRow' grid gridsize cell (counter + 1) (x,y)

placeOppositeCells :: Grid -> Cell -> [Pos] -> [Bool] -> Pos -> Grid
placeOppositeCells grid _ _ [] _ = grid
placeOppositeCells grid cell (p:positions) (b:boolArray) (x,y) = 
    if b 
    then placeOppositeCells (placeCell grid p cell (x,y)) cell positions boolArray (x,y)
    else placeOppositeCells grid cell positions boolArray (x,y)

tryPlacements :: Grid -> Pos -> Cell -> [Pos] -> [Bool]
tryPlacements _ _ _ [] = []
tryPlacements grid gridsize cell ((x,y):emptys)
    | tryPlacements' (placeCell grid (x,y) cell gridsize) gridsize cell x = True:(tryPlacements grid gridsize cell emptys)
    | otherwise = False:(tryPlacements grid gridsize cell emptys)

tryPlacements' grid (sizerow, sizecol) cell pos
    | pos == sizerow = False
    | let oppositeCellAmount = count (opposite cell) (grid!!pos),
      and [count cell (grid!!pos) == sizecol `div` 2,
           oppositeCellAmount < sizecol `div` 2 - 1,
           checkForPossibleTripple (grid!!pos) (opposite cell) 0 0] = True
    | otherwise = False

count :: Cell -> [Cell] -> Int
count cell line = length (filter (== cell) line) 

-- Basic technique 4, completes a row/column so that the number of X's and O's are equal in each row/column.
solveComplete :: Grid -> Pos -> Grid
solveComplete grid (sizerow,sizecol) = transpose (solveCompleteRow (transpose (solveCompleteRow grid 0 (sizerow,sizecol))) 0 (sizecol,sizerow))

solveCompleteRow :: Grid -> Int -> Pos -> Grid
solveCompleteRow grid row (sizerow, sizecol)
    | row < sizerow = solveCompleteRow (solveCompleteRow' grid (count O (grid!!row)) (count X (grid!!row)) (getCellRowPos grid E row (sizerow, sizecol)) (sizerow, sizecol)) (row+1) (sizerow, sizecol)
    | row == sizerow = grid

solveCompleteRow' :: Grid -> Int -> Int -> [Pos] -> Pos -> Grid
solveCompleteRow' grid amountO amountX emptyPos (sizerow, sizecol)
    | emptyPos == [] = grid
    | amountO == sizecol `div` 2 = solveCompleteRow' (placeCell grid (head emptyPos) X (sizerow, sizecol)) amountO (amountX+1) (tail emptyPos) (sizerow,sizecol)
    | amountX == sizecol `div` 2 = solveCompleteRow' (placeCell grid (head emptyPos) O (sizerow, sizecol)) (amountO+1) amountX (tail emptyPos) (sizerow,sizecol)
    | otherwise = grid

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------


-- Checks if the grid:
-- 1. has equal amounts of X's and O's in each row and column
-- 2. has no triples
-- 3. has no two rows or columns that are identical 
validGrid :: Grid -> Pos -> Bool
validGrid grid (x,y) = 
    -- for each row col, check number of X and O < half size.
    _validGridOccurenceCountRows grid 0 (x,y) && 
    _validGridOccurenceCountRows (transpose grid) 0 (y,x) && 
    -- for each row col, check for triples.
    _validGridNoTripleRow grid 0 (x,y) &&
    _validGridNoTripleRow (transpose grid) 0 (y,x) &&
    -- for each row col, check duplicate row/col.
    _validGridNoDuplicateRows grid 0 (x,y) &&
    _validGridNoDuplicateRows (transpose grid) 0 (y,x)

_validGridOccurenceCountRows :: Grid -> Int -> Pos -> Bool
_validGridOccurenceCountRows grid counter (x,y) 
    | counter == x = True
    | and [count X (grid!!counter) <= (y `div` 2), count O (grid!!counter) <= (y `div` 2)] = _validGridOccurenceCountRows grid (counter+1) (x,y)
    | otherwise = False
    
_validGridNoTripleRow grid counter (x,y)
    | counter == x = True
    | not (lineContainsTripple (grid!!counter)) = _validGridNoTripleRow grid (counter+1) (x,y)
    | otherwise = False

lineContainsTripple :: [Cell] -> Bool
lineContainsTripple (c:cells) = lineContainsTripple' (tail cells) c (head cells)

lineContainsTripple' :: [Cell] -> Cell -> Cell -> Bool
lineContainsTripple' [] _ _ = False
lineContainsTripple' (c3:cells) c1 c2
    | and [c1 /= E, c1 == c2, c2 == c3] = True
    | otherwise = lineContainsTripple' cells c2 c3

_validGridNoDuplicateRows :: Grid -> Int -> Pos -> Bool
_validGridNoDuplicateRows grid counter (x,y)
    | counter == x = True
    | not (lineIsDuplicate (grid!!counter) (removeLineFromGrid grid counter)) = _validGridNoDuplicateRows grid (counter+1) (x,y)
    | otherwise = False
    
lineIsDuplicate' :: [Cell] -> [Cell] -> Bool
lineIsDuplicate' [] [] = True
lineIsDuplicate' (l:line) (d:dup)
    | l == d = lineIsDuplicate' line dup
    | otherwise = False

lineIsDuplicate :: [Cell] -> Grid -> Bool
lineIsDuplicate _ [] = False
lineIsDuplicate line (g:grid) = if and [(count E line) == 0,(lineIsDuplicate' line g)]
    then True
    else lineIsDuplicate line grid

removeLineFromGrid :: Grid -> Int -> Grid
removeLineFromGrid [] _ = []
removeLineFromGrid (line:grid) 0 = grid
removeLineFromGrid grid row = let (ys,zs) = splitAt row grid in ys ++ (tail zs)

-- Checks if grid contains pattern OO or XX horizontally and vertically.
checkDouble :: Grid -> Pos -> Bool
checkDouble grid (sizerow,sizecol) = or [checkDoubleRow grid (getCellPos grid X (sizerow,sizecol)) (sizerow,sizecol),
                                         checkDoubleRow grid (getCellPos grid O (sizerow,sizecol)) (sizerow,sizecol),
                                         checkDoubleRow (transpose grid) (getCellPos (transpose grid) X (sizecol,sizerow)) (sizecol,sizerow),
                                         checkDoubleRow (transpose grid) (getCellPos (transpose grid) O (sizecol,sizerow)) (sizecol,sizerow)]

checkDoubleRow :: Grid -> [Pos] -> Pos -> Bool
checkDoubleRow _ [] _ = False
checkDoubleRow grid ((x,y):pos) gridsize =
    if and [isValidPos (x,y+1) gridsize, getCell grid (x,y) == getCell grid (x, y+1), or [ and [isValidPos (x, y-1) gridsize, getCell grid (x,y-1) == E], and [isValidPos (x, y+2) gridsize, getCell grid (x,y+2) == E]]]
    then True
    else checkDoubleRow grid pos gridsize

-- Checks if grid contains pattern O.O or X.X horizontally and vertically.
checkInbetween :: Grid -> Pos -> Bool
checkInbetween grid (sizerow,sizecol) = or [checkInbetweenRow grid (getCellPos grid X (sizerow,sizecol)) (sizerow,sizecol),
                                            checkInbetweenRow grid (getCellPos grid O (sizerow,sizecol)) (sizerow,sizecol),
                                            checkInbetweenRow (transpose grid) (getCellPos (transpose grid) X (sizecol,sizerow)) (sizecol,sizerow),
                                            checkInbetweenRow (transpose grid) (getCellPos (transpose grid) O (sizecol,sizerow)) (sizecol,sizerow)]

checkInbetweenRow :: Grid -> [Pos] -> Pos -> Bool
checkInbetweenRow _ [] _ = False
checkInbetweenRow grid ((x,y):pos) gridsize = 
    if and [isValidPos (x, y+2) gridsize, getCell grid (x,y+2) == getCell grid (x,y), isEmpty grid (x, y+1) gridsize]
    then True
    else checkInbetweenRow grid pos gridsize

-- Checks if a forbidden triple one or two steps later is present.
checkForbidden :: Grid -> Pos -> Bool
checkForbidden grid (sizerow, sizecol)  = or [checkForbidden' grid (sizerow, sizecol)  X 0,
                                              checkForbidden' grid (sizerow, sizecol)  O 0,
                                              checkForbidden' (transpose grid) (sizecol, sizerow)  X 0,
                                              checkForbidden' (transpose grid) (sizecol, sizerow)  O 0]

checkForbidden' :: Grid -> Pos -> Cell -> Int -> Bool
checkForbidden' grid (sizerow, sizecol) cell counter
    | let bool = checkForForbiddenLine grid (sizerow, sizecol) cell counter, bool = True
    | counter == sizerow = False
    | otherwise = checkForbidden' grid (sizerow, sizecol) cell (counter+1)

checkForForbiddenLine :: Grid -> Pos -> Cell -> Int -> Bool
checkForForbiddenLine grid (sizerow, sizecol) cell pos
    | pos == sizerow = False
    | let oppositeCellAmount = count (opposite cell) (grid!!pos),
      and [count cell (grid!!pos) == sizecol `div` 2 - 1,
           oppositeCellAmount < sizecol `div` 2 - 1,
           checkForPossibleTripple (grid!!pos) (opposite cell) 0 0] = True -- possible to apply technique 3
    | otherwise = False

checkForPossibleTripple :: [Cell] -> Cell -> Int -> Int -> Bool
checkForPossibleTripple [] _ _ _ = False
checkForPossibleTripple (c:cells) cell cellamount emptyamount
    | and [cellamount >= 1, emptyamount >= 2] = True 
    | c == cell = checkForPossibleTripple cells cell (cellamount+1) emptyamount
    | c == E = checkForPossibleTripple cells cell cellamount (emptyamount+1)
    | c == opposite cell = checkForPossibleTripple cells cell 0 0
    | otherwise = False

-- Checks if a row or column can be completed.
checkComplete :: Grid -> Pos -> Bool
checkComplete grid (sizerow,sizecol) = or [checkCompleteRow grid 0 (sizerow,sizecol),
                                           checkCompleteRow (transpose grid) 0 (sizecol,sizerow)]

checkCompleteRow :: Grid -> Int -> Pos -> Bool
checkCompleteRow grid row (sizerow,sizecol)
    | row < sizerow =
        if or[and [count X (grid!!row) == sizecol `div` 2, count E (grid!!row) > 0], and [count O (grid!!row) == sizecol `div` 2, count E (grid!!row) > 0]]
        then True
        else checkCompleteRow grid (row+1) (sizerow,sizecol)
    | row == sizerow = False

-- Checks if there are no empty cells.
checkSolved :: Grid -> Pos -> Bool
checkSolved grid gridsize 
    | countCell grid E gridsize == 0 = True
    | otherwise = False

-- If no technique can be used, it places an X on the first empty cell on the grid and tries solving the grid.
-- If it fails, it backtracks and places an O instead and tries solving it. Tries to solve the grid by trial-and-error.
hitOrMiss :: Grid -> Pos -> Maybe Grid
hitOrMiss grid gridsize = do
    let emptyPos = getCellPos grid E gridsize
    let gridX = placeCell grid (head emptyPos) X gridsize
    let gridO = placeCell grid (head emptyPos) O gridsize
    case (solveTakuzu gridX gridsize 0) of
        Nothing -> (solveTakuzu gridO gridsize 0)
        Just b -> Just b

-- Checks which technique can be used on the grid or the state of the grid (if solved or invalid) and returns a corresponding int.
-- 0 = The grid is invalid (contains unequal amounts of X's or O's, triples or two rows/columns are identical).
-- 1 = The grid is solved, i.e. does not contain any empty cells and is a valid grid.
-- 2 = Can use basic technique 1 on the grid.
-- 3 = Can use basic technique 2 on the grid.
-- 4 = Can use basic technique 3 on the grid.
-- 5 = Can use basic technique 2 on the grid.
-- 6 = The grid is unsolved and no basic technique can be used on the grid.
checkTechnique :: Grid -> Pos -> Int
checkTechnique grid gridsize
    | not (validGrid grid gridsize) = 0
    | and [checkSolved grid gridsize, validGrid grid gridsize] = 1
    | checkDouble grid gridsize = 2
    | checkInbetween grid gridsize = 3
    | checkForbidden grid gridsize  = 4
    | checkComplete grid gridsize = 5
    | otherwise = 6

-- Uses a technique on the grid or by trial-and-error, or returns the grid if solved or nothing if grid is invalid.
solveTakuzu' :: Int -> Grid -> Pos -> Maybe Grid
solveTakuzu' 0 grid gridsize = Nothing
solveTakuzu' 1 grid gridsize = Just grid
solveTakuzu' 2 grid gridsize = Just (solveDouble grid gridsize)
solveTakuzu' 3 grid gridsize = Just (solveInbetween grid gridsize)
solveTakuzu' 4 grid gridsize = Just (solveForbidden grid gridsize)
solveTakuzu' 5 grid gridsize = Just (solveComplete grid gridsize)
solveTakuzu' 6 grid gridsize = hitOrMiss grid gridsize

-- Tries solving the grid by using techniques or by trial-and-error. If the grid can't be solved, returns nothing.
solveTakuzu :: Grid -> Pos -> Int -> Maybe Grid
solveTakuzu grid _ 1 = Just grid
solveTakuzu grid gridsize _ = do
    case (solveTakuzu' (checkTechnique grid gridsize) grid gridsize) of
        Nothing -> Nothing
        Just g -> (solveTakuzu g gridsize (checkTechnique grid gridsize))


main = do
    line <- getLine
    let [a,b] = words line
    let sizerow = read a :: Int
    let sizecol = read b :: Int
    g <- readLines []
    let gr = createGrid g []

    case (solveTakuzu gr (sizerow,sizecol) 0) of
        Nothing -> putStrLn "Could not solve the given puzzle"
        Just b -> printGrid b