-- Damas em Haskell com Captura
-- Autores: 
-- Marcos Paulo Rodrigues da Silvas (202165556C)
-- João Victor Wayand De Jesus Dias (201935012)
{-# LANGUAGE BlockArguments #-}

import Data.Char (chr, ord, toUpper)
import Data.List (intercalate, maximumBy)
import Data.Maybe (fromMaybe, isJust, isNothing)
import Control.Concurrent (threadDelay)
import System.CPUTime (getCPUTime)
import Data.Ord (comparing)


-- Data types
data Player = PlayerA | PlayerB deriving (Eq, Show)
data PieceType = Man | King deriving (Eq, Show)
data Piece = Piece Player PieceType deriving (Eq, Show)
data Square = Dark (Maybe Piece) | Light deriving (Eq, Show)
data PlayerType = Human | AI deriving (Eq, Show)
type Board = [[Square]]
type Position = (Int, Int) -- (row, col)


data GameState = GameState {
    board :: Board,
    currentPlayer :: Player
} deriving (Show)

-- Constants
boardSize :: Int
boardSize = 8

-- Board initialization
initialBoard :: Board
initialBoard = [ [initialSquare r c | c <- [0..7]] | r <- [0..7] ]
  where
    initialSquare row col
        | even (row + col) = Dark (initialPiece row)
        | otherwise = Light
    initialPiece row
        | row <= 2 = Just (Piece PlayerA Man)
        | row >= 5 = Just (Piece PlayerB Man)
        | otherwise = Nothing

-- Display functions
showSquare :: Square -> String
showSquare Light = " . "
showSquare (Dark Nothing) = "   "
showSquare (Dark (Just (Piece PlayerA Man))) = " a "
showSquare (Dark (Just (Piece PlayerA King))) = " A "
showSquare (Dark (Just (Piece PlayerB Man))) = " b "
showSquare (Dark (Just (Piece PlayerB King))) = " B "

showBoard :: Board -> String
showBoard b =
    let header = "  " ++ concat [" " ++ [chr (c + ord 'A')] ++ " " | c <- [0..7]]
        rows = [show (8 - r) ++ " " ++ concatMap showSquare row | (r, row) <- zip [0..] (reverse b)]
    in unlines (header : rows)

showPlayer :: Player -> String
showPlayer PlayerA = "Jogador A"
showPlayer PlayerB = "Jogador B"

-- Get and set board positions
getSquare :: Board -> Position -> Maybe Square
getSquare b (r, c)
    | r < 0 || r >= boardSize || c < 0 || c >= boardSize = Nothing
    | otherwise = Just ((b !! r) !! c)

setSquare :: Board -> Position -> Square -> Board
setSquare b (r, c) sq =
    take r b ++ [take c (b !! r) ++ [sq] ++ drop (c + 1) (b !! r)] ++ drop (r + 1) b

-- Utility functions
inBounds :: Position -> Bool
inBounds (r, c) = r >= 0 && r < boardSize && c >= 0 && c < boardSize

isEmpty :: Board -> Position -> Bool
isEmpty b pos = case getSquare b pos of
    Just (Dark Nothing) -> True
    _ -> False

isOpponent :: Player -> Maybe Piece -> Bool
isOpponent p (Just (Piece p' _)) = p /= p'
isOpponent _ _ = False

-- Capture logic
type CapturePath = ([Position], [Position]) -- path, captured positions

jumpDirections :: [(Int, Int)]
jumpDirections = [(-1, -1), (-1, 1), (1, -1), (1, 1)]

capturePaths :: GameState -> Position -> [CapturePath]
capturePaths gs pos =
  case getSquare (board gs) pos of
    Just (Dark (Just (Piece p pieceType))) | p == currentPlayer gs ->
      captureFrom pos [] []
      where
        b = board gs

        captureFrom :: Position -> [Position] -> [Position] -> [CapturePath]
        captureFrom curr path caps =
          let moves = case pieceType of
                Man  -> manCaptures curr caps
                King -> kingCaptures curr caps
          in case moves of
              [] -> [(reverse (curr:path), caps)]
              _  -> concat [ captureFrom dest (curr:path) (capturedPos:caps)
                           | (dest, capturedPos) <- moves ]

        getPiece :: Position -> Maybe Piece
        getPiece p = case getSquare b p of
          Just (Dark mp) -> mp
          _ -> Nothing

        manCaptures :: Position -> [Position] -> [(Position, Position)]
        manCaptures (r, c) captured =
          [ (dest, enemy) |
              (dr, dc) <- jumpDirections,
              let enemy = (r + dr, c + dc),
              let dest = (r + 2*dr, c + 2*dc),
              inBounds enemy, inBounds dest,
              isOpponent p (getPiece enemy),
              isEmpty b dest,
              enemy `notElem` captured ]

        kingCaptures :: Position -> [Position] -> [(Position, Position)]
        kingCaptures (r, c) captured = concatMap exploreDir jumpDirections
          where
            exploreDir (dr, dc) =
              let ray = [(r + i*dr, c + i*dc) | i <- [1..7], inBounds (r + i*dr, c + i*dc)]
                  findEnemy [] _ = []
                  findEnemy (p':ps) before
                    | isOpponent p (getPiece p') && p' `notElem` captured =
                        let after = takeWhile (isEmpty b) ps
                        in [ (dest, p') | dest <- after ]
                    | isEmpty b p' = findEnemy ps (p':before)
                    | otherwise = []
              in findEnemy ray []
    _ -> []


-- Valid move generation
validMoves :: GameState -> Position -> [Position]
validMoves gs pos =
  case getSquare (board gs) pos of
    Just (Dark (Just (Piece player pieceType))) | player == currentPlayer gs ->
      let caps = capturePaths gs pos
      in if any (\(_, cs) -> not (null cs)) caps
         then [last path | (path, _) <- caps, length path > 1]
         else case pieceType of
         Man  -> manMoves player pos (board gs)
         King -> kingMoves pos (board gs)
    _ -> []

manMoves :: Player -> Position -> Board -> [Position]
manMoves p (r,c) b = filter (isEmpty b) $ case p of
    PlayerA -> [(r+1, c-1), (r+1, c+1)]
    PlayerB -> [(r-1, c-1), (r-1, c+1)]

kingMoves :: Position -> Board -> [Position]
kingMoves (r, c) b = concatMap (ray (r, c)) jumpDirections
  where
    ray (x, y) (dr, dc) =
      let next = (x + dr, y + dc)
      in if inBounds next && isEmpty b next
         then next : ray next (dr, dc)
         else []

-- Move execution (with capture)
movePiece :: GameState -> Position -> Position -> Maybe GameState
movePiece gs from to =
  case getSquare (board gs) from of
    Just (Dark (Just (Piece p t))) | p == currentPlayer gs ->
      let allCaps = filter (not . null . snd) (capturePaths gs from)
          maxCaptures = if null allCaps then 0 else maximum (map (length . snd) allCaps)
          bestCaps = filter ((== maxCaptures) . length . snd) allCaps
      in case filter ((== to) . last . fst) bestCaps of
            ((path, captured):_) ->
              let b1 = foldl (\acc pos -> setSquare acc pos (Dark Nothing)) (board gs) captured
                  b2 = setSquare (setSquare b1 from (Dark Nothing)) to (Dark (Just (Piece p (promote p t to))))
                  nextP = if p == PlayerA then PlayerB else PlayerA
              in Just GameState { board = b2, currentPlayer = nextP }
            [] -> if maxCaptures == 0 && to `elem` (case t of Man -> manMoves p from (board gs); King -> kingMoves from (board gs))
                  then let b1 = setSquare (board gs) from (Dark Nothing)
                           b2 = setSquare b1 to (Dark (Just (Piece p (promote p t to))))
                           nextP = if p == PlayerA then PlayerB else PlayerA
                       in Just GameState { board = b2, currentPlayer = nextP }
                  else Nothing
    _ -> Nothing

promote :: Player -> PieceType -> Position -> PieceType
promote PlayerA Man (r, _) | r == 7 = King
promote PlayerB Man (r, _) | r == 0 = King
promote _ t _ = t

-- Game loop
parsePos :: String -> Maybe Position
parsePos [col, rowChar]
    | toUpper col `elem` ['A'..'H'] && row `elem` [1..8] = Just (row - 1, ord (toUpper col) - ord 'A')
    | otherwise = Nothing
  where row = read [rowChar] :: Int
parsePos _ = Nothing

gameLoop :: GameState -> (PlayerType, PlayerType) -> IO ()
gameLoop gs (playerAType, playerBType) = do
    putStrLn $ "Jogador atual: " ++ showPlayer (currentPlayer gs)
    putStrLn $ showBoard (board gs)
    let currentType = case currentPlayer gs of
                        PlayerA -> playerAType
                        PlayerB -> playerBType
    case currentType of
      Human -> do
        let allCaptures = [ (from, path, cs) |
                              r <- [0..7], c <- [0..7],
                              let from = (r,c),
                              Just (Dark (Just (Piece p _))) <- [getSquare (board gs) from],
                              p == currentPlayer gs,
                              (path, cs) <- capturePaths gs from,
                              not (null cs) ]
            maxCap = if null allCaptures then 0 else maximum (map (length . (\(_, _, cs) -> cs)) allCaptures)
            bestCaptures = [ (from, path) | (from, path, cs) <- allCaptures, length cs == maxCap ]

            posToStr (r, c) = [chr (c + ord 'A')] ++ show (r + 1)
            bestMovesStr = [ (posToStr f, posToStr (last path)) | (f, path) <- bestCaptures ]

        if maxCap > 0 then
          putStrLn $ "Captura máxima obrigatória disponível com " ++ show maxCap ++ " movimentos: " ++ show bestMovesStr
        else return ()

        putStrLn "Digite o movimento (ex: A3 B4) ou 'Sair':"
        input <- getLine
        if map toUpper input == "SAIR"
          then putStrLn "Jogo encerrado."
          else do
            let moveWords = words input
            if length moveWords /= 2 then invalid else do
              let from = parsePos (moveWords !! 0)
                  to   = parsePos (moveWords !! 1)
              case (from, to) of
                (Just f, Just t) ->
                  if maxCap > 0 && not (any (\(f', path) -> f == f' && t == last path) bestCaptures)
                    then putStrLn "Você deve jogar uma das capturas obrigatórias com maior número de peças." >> gameLoop gs (playerAType, playerBType)
                    else case movePiece gs f t of
                      Just newGs -> gameLoop newGs (playerAType, playerBType)
                      Nothing    -> invalid
                _ -> invalid

      AI -> do
        threadDelay 500000
        move <- selectAIMove gs  -- extrai a ação IO que retorna Maybe (Position, Position)
        case move of
          Just (from, to) -> do
            putStrLn $ "IA jogou de " ++ showPos from ++ " para " ++ showPos to
            case movePiece gs from to of
              Just newGs -> gameLoop newGs (playerAType, playerBType)
              Nothing    -> putStrLn "Movimento inválido pela IA. Fim de jogo."
          Nothing -> putStrLn $ "Sem movimentos válidos para " ++ showPlayer (currentPlayer gs) ++ ". Fim de jogo."
  where
    invalid = putStrLn "Movimento inválido" >> gameLoop gs (playerAType, playerBType)
    showPos (r, c) = [chr (c + ord 'A')] ++ show (r + 1)


-- Avalia um estado do tabuleiro para uma peça específica
evaluateBoardPosition :: Position -> Player -> PieceType -> Int
evaluateBoardPosition (r, c) player pieceType =
    let
        -- Prioridade: Ir para a promoção
        promoBonus = case player of
            PlayerA -> if r == 7 && pieceType == Man then 100 else 0
            PlayerB -> if r == 0 && pieceType == Man then 100 else 0
        -- Prioridade: Centro do tabuleiro
        centerBonus = if (r >= 2 && r <= 5) && (c >= 2 && c <= 5) then 20 else 0
        -- Prioridade: Avançar (para peões)
        advanceScore = case player of
            PlayerA -> r * 2 -- Quanto mais pra frente (maior r), melhor para PlayerA
            PlayerB -> (boardSize - 1 - r) * 2 -- Quanto mais pra frente (menor r), melhor para PlayerB
        -- Prioridade: Dama é mais valiosa
        kingBonus = if pieceType == King then 50 else 0
    in
        promoBonus + centerBonus + advanceScore + kingBonus


-- Avaliação de Movimento Específico
evaluateMove :: GameState -> (Position, Position) -> Int
evaluateMove gs (from, to) =
    let
        currentBoard = board gs
        movingPiece = case getSquare currentBoard from of
            Just (Dark (Just p)) -> p
            _ -> error "evaluateMove: No piece at 'from' position." 

        (Piece player pieceType) = movingPiece
        -- 1. Pontuação para CAPTURA
        -- Calculamos se este movimento específico resulta em uma captura e quantas peças
        numCaptured = case filter ((== to) . last . fst) (capturePaths gs from) of
                         [] -> 0 
                         ((_, cs):_) -> length cs 
        -- 2. Pontuação para PROMOÇÃO
        promoScore = if pieceType == Man && promote player Man to == King then 200 else 0
        -- 3. Pontuação para AVANÇO (Peões)
        advanceScore = if pieceType == Man then
                           case player of
                               PlayerA -> (fst to - fst from) * 5 -- Quanto mais avança (maior 'r'), melhor para A
                               PlayerB -> (fst from - fst to) * 5 -- Quanto mais avança (menor 'r'), melhor para B
                       else 0 
        -- Privilegia movimentos da Dama
        kingPresenceScore = if pieceType == King then 50 else 0
    in
        (numCaptured * 1000) + promoScore + advanceScore + kingPresenceScore

-- IA prioriza capturas máximas e movimentos com maior pontuação descrita
selectAIMove :: GameState -> IO (Maybe (Position, Position))
selectAIMove gs = do
    let b = board gs
        p = currentPlayer gs
        playerPieces = [ pos | r <- [0..7], c <- [0..7],
                           let pos = (r,c),
                           Just (Dark (Just (Piece p' _))) <- [getSquare b pos],
                           p' == p ]
        allCaptures = [ (from, path, cs) |
                          from <- playerPieces,
                          (path, cs) <- capturePaths gs from,
                          not (null cs) ]
                          
    if not (null allCaptures)
        then do
            let maxCapturedCount = maximum (map (length . (\(_, _, cs) -> cs)) allCaptures)
                bestCaptures = filter ((== maxCapturedCount) . length . (\(_, _, cs) -> cs)) allCaptures
                bestCaptureMoves = [ (from, last path) | (from, path, _) <- bestCaptures ]
            let ratedMoves = [ (evaluateMove gs m, m) | m <- bestCaptureMoves ]
            if null ratedMoves
                then return Nothing
                else return $ Just (snd (maximumBy (comparing fst) ratedMoves))
        else do
            -- Se não houver capturas, encontre todos os movimentos normais válidos
            let allNormalMoves = [ (from, to) |
                                   from <- playerPieces,
                                   to <- validMoves gs from ]
            if null allNormalMoves
                then return Nothing
                else do
                    -- Escolhe o de maior pontuação possível
                    let ratedMoves = [ (evaluateMove gs m, m) | m <- allNormalMoves ]
                    return $ Just (snd (maximumBy (comparing fst) ratedMoves))

-- Loop de IA vs IA
gameLoopIA :: GameState -> IO ()
gameLoopIA gs = do
    putStrLn $ "Jogador atual: " ++ showPlayer (currentPlayer gs)
    putStrLn $ showBoard (board gs)
    threadDelay 1000000  -- 0,5 segundos
    move <- selectAIMove gs
    case move of
      Just (from, to) -> do
        putStrLn $ "IA jogou de " ++ showPos from ++ " para " ++ showPos to
        case movePiece gs from to of
          Just newGs -> gameLoopIA newGs
          Nothing -> putStrLn "Movimento inválido pela IA. Fim de jogo."
      Nothing -> putStrLn $ "Sem movimentos válidos para " ++ showPlayer (currentPlayer gs) ++ ". Fim de jogo."
  where
    showPos (r, c) = [chr (c + ord 'A')] ++ show (r + 1)

-- Menu
mainMenu :: IO ()
mainMenu = do
    putStrLn "==== MENU ===="
    putStrLn "1. Jogar contra IA"
    putStrLn "2. Assistir (IA vs IA)"
    putStrLn "3. Sair"
    putStrLn "Escolha uma opção (1, 2 ou 3):"
    choice <- getLine
    case choice of
        "1" -> do
            putStrLn "Você quer jogar como o jogador A ou B? (Digite A ou B):"
            playerChoice <- getLine
            putStrLn "Digite 'Sair' na sua rodada para desistir."
            case map toUpper playerChoice of
              "A" -> gameLoop (GameState initialBoard PlayerA) (Human, AI)
              "B" -> gameLoop (GameState initialBoard PlayerA) (AI, Human)
              _   -> putStrLn "Escolha inválida. Voltando ao menu." >> mainMenu
        "2" -> gameLoopIA (GameState initialBoard PlayerA)
        "3" -> putStrLn "Saindo do jogo."
        _   -> putStrLn "Opção inválida." >> mainMenu


main :: IO ()
main = do
    putStrLn "Bem-vindo ao jogo de Damas!"
    mainMenu
