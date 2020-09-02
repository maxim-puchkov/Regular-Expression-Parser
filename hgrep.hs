--
-- Maxim Puchkov
-- 301314335
-- CMPT 384 Assignment 1 (Redo)
--
-- Regular Expressions in Haskell
-- Using Glushkov's Algorithm
-- Assignment Redo with instructor's solutions.
--

import System.Environment
import System.IO (stdout,stderr,hPutStr,hPutStrLn)
import Data.Bits
import Data.List





-- 1. An algebraic data type for regular expressions

data RE = Epsilon | Any | Option RE | Ch Char | Seq RE RE | Alt RE RE | Star RE | Plus RE | Group RE deriving Show





-- 2. Regular expression matching

match :: RE -> [Char] -> Bool

glushkovMatch :: [Char] -> Int -> Int -> [([Char], Int)] -> [(Int, Int)] -> Bool
nextState :: Char -> Int -> [([Char], Int)] -> [(Int, Int)] -> Int

firstSym :: RE -> [Int]
lastSym :: RE -> [Int]
pairSym :: RE -> [[Int]]
symbols :: RE -> [[Char]]
uniqueSymbols :: RE -> [[Char]]

indexInRE :: Int -> Char -> RE -> [Int]
indexOf :: Char -> RE -> [Int]

numState :: [Int] -> Int
posState :: Int -> [Int]

bitSetPositions :: RE -> [[Char]] -> [([Char], [Int])]
bitSet :: [([Char], [Int])] -> [([Char], Int)]
bitStateFor :: Char -> [([Char], Int)] -> Int

allTransitionSets :: [[Int]] -> [[Int]] -> [(Int, [Int])]
groupedTransitionSets :: [[Int]] -> [(Int, [Int])]
generateTransitionSet :: [(Int, [Int])] -> [(Int, Int)]
transitionSet :: RE -> [(Int, Int)]
transitionSetEntryFor :: Int -> [[Int]] -> [Int]
transitionStateFor :: Int -> [(Int, Int)] -> Int


countCh Epsilon = 0
countCh (Ch c) = 1
countCh (Any) = 1
countCh (Option r) = countCh r
countCh (Plus r) = countCh r
countCh (Seq r1 r2) = (countCh r1) + (countCh r2)
countCh (Alt r1 r2) = (countCh r1) + (countCh r2)
countCh (Star r) = countCh r
countCh (Group r) = countCh r


matchesEmpty Epsilon = True
matchesEmpty (Ch c) = False
matchesEmpty (Any) = False
matchesEmpty (Option r) = True
matchesEmpty (Plus r) = False
matchesEmpty (Seq r1 r2) = (matchesEmpty r1) && (matchesEmpty r2)
matchesEmpty (Alt r1 r2) = (matchesEmpty r1) || (matchesEmpty r2)
matchesEmpty (Star r) = True
matchesEmpty (Group r) = matchesEmpty r


-- First symbols positions
firstWithIndex i (Epsilon) = []
firstWithIndex i (Ch c) = [i]
firstWithIndex i (Any) = [i]
firstWithIndex i (Option r) = [i]
firstWithIndex i (Seq r1 r2)
  | matchesEmpty r1 = (firstWithIndex i r1) ++ (firstWithIndex (i + countCh r1) r2)
  | otherwise       = (firstWithIndex i r1)
firstWithIndex i (Alt r1 r2) = (firstWithIndex i r1) ++ (firstWithIndex (i + countCh r1) r2)
firstWithIndex i (Star r) = firstWithIndex i r
firstWithIndex i (Plus r) = firstWithIndex i r
firstWithIndex i (Group r) = firstWithIndex i r


firstSym r = firstWithIndex 1 r


-- Last symbols positions
lastWithIndex i (Epsilon) = [i]
lastWithIndex i (Ch c) = [i]
lastWithIndex i (Any) = [i]
lastWithIndex i (Option r) = lastWithIndex i r
lastWithIndex i (Seq r1 r2)
  | (matchesEmpty r2 && matchesEmpty r1) = (lastWithIndex i r1) ++ (lastWithIndex (i + countCh r1) r2)
  | matchesEmpty r2 = (lastWithIndex i r1) ++ (lastWithIndex (i + countCh r1) r2)
  | otherwise       = (lastWithIndex (i + countCh r1) r2)
lastWithIndex i (Alt r1 r2) = (lastWithIndex i r1) ++ (lastWithIndex (i + countCh r1) r2)
lastWithIndex i (Star r) = lastWithIndex i r
lastWithIndex i (Plus r) = lastWithIndex i r
lastWithIndex i (Group r) = lastWithIndex i r


lastSym r
  | matchesEmpty r = 0 : lastWithIndex 1 r
  | otherwise      = lastWithIndex 1 r


-- Determine positions of pairs
pairWithIndex i (Epsilon) = []
pairWithIndex i (Ch c) = []
pairWithIndex i (Any) = []
pairWithIndex i (Option r) = pairWithIndex i r
pairWithIndex i (Seq r1 r2)
  | matchesEmpty r2 =
    [[i + countCh r1 - 1, i + countCh r1 + countCh r2]]
    ++ (offset (i) (countCh r1 - 1) (firstSym r2)) ++ [[i + countCh r1 - 1, i + countCh r1]] ++ (pairWithIndex i r1) ++ (pairWithIndex (i + countCh r1) r2)
  | matchesEmpty r1 =
    (offset (i) (countCh r1 - 1) (firstSym r2)) ++ [[i + countCh r1 - 1, i + countCh r1]] ++ (pairWithIndex i r1) ++ (pairWithIndex (i + countCh r1) r2)
  | otherwise       =
    [[i + countCh r1 - 1, i + countCh r1]] ++ (pairWithIndex i r1) ++ (pairWithIndex (i + countCh r1) r2)
pairWithIndex i (Alt r1 r2) = (pairWithIndex i r1) ++ (pairWithIndex (i + countCh r1) r2)
pairWithIndex i (Star r) = repeatedPairWithIndex i r ++ [[i + countCh r - 1, i]]
pairWithIndex i (Plus r) = repeatedPairWithIndex i r ++ [[i + countCh r - 1, i]]
pairWithIndex i (Group r) = pairWithIndex i r


-- Additional rules for repeated regex, e.g. (a|b)* could have pairs "aa", "ab", "ba", "bb"
repeatedPairWithIndex i (Epsilon) = []
repeatedPairWithIndex i (Ch c) = []
repeatedPairWithIndex i (Any) = []
repeatedPairWithIndex i (Option r) = []
repeatedPairWithIndex i (Alt r1 r2)
  = [[i + (countCh r1) - 1, i]] ++ [[i + (countCh r1) - 1, i + countCh r1]] ++ [[i + countCh r1, i + countCh r1 + countCh r2 - 1]] ++ [[i + countCh r1 + countCh r2 - 1, i + countCh r1]] ++ (pairWithIndex i r1) ++ (pairWithIndex (i + countCh r1) r2)
repeatedPairWithIndex i (Seq r1 r2)
  | matchesEmpty r1 && matchesEmpty r2 =
    (offset (i) (countCh r1 - 1) (firstSym r2)) ++ (offset (i + countCh r1) (-(countCh r1 + 1)) (firstSym r1))
    ++ [[i + countCh r1 - 1, i]] ++ (pairWithIndex i r1) ++ [[i + countCh r1 - 1, i + countCh r1]] ++ (pairWithIndex (i + countCh r1) r2) ++ [[i + countCh r1 - 1, i + countCh r1]] ++ [[i + countCh r1, i + countCh r2]] ++ (pairWithIndex i r1) ++ (pairWithIndex (i + countCh r1) r2)
  | matchesEmpty r2 =
    (offset (i) (countCh r1 - 1) (firstSym r2))
    ++ [[i + countCh r1 - 1, i]] ++ (pairWithIndex i r1) ++ [[i + countCh r1 - 1, i + countCh r1]] ++ (pairWithIndex (i + countCh r1) r2)
  | matchesEmpty r1 =
    (offset (i + countCh r1) (-(countCh r1 + 1)) (firstSym r1))
    ++ [[i + countCh r1 - 1, i + countCh r1]] ++ [[i + countCh r1, i + countCh r2]] ++ (pairWithIndex i r1) ++ (pairWithIndex (i + countCh r1) r2)
  | otherwise       =
    [[i + countCh r1 - 1, i + countCh r1]] ++ (pairWithIndex i r1) ++ (pairWithIndex (i + countCh r1) r2)
repeatedPairWithIndex i (Star r) = repeatedPairWithIndex i r
repeatedPairWithIndex i (Plus r) = repeatedPairWithIndex i r
repeatedPairWithIndex i (Group r) = repeatedPairWithIndex i r


pairSym r = map head (group (sort (pairWithIndex 1 r)))


offset :: Int -> Int -> [Int] -> [[Int]]
offset i l [] = []
offset i length (x:fs) = (offset i length fs) ++ [i, i + length + x] : []


-- Get symbols from Regex
symbols (Epsilon) = []
symbols (Ch c) = [[c]]
symbols (Any) = []
symbols (Option r) = symbols r
symbols (Seq r1 r2) = symbols r1 ++ symbols r2
symbols (Alt r1 r2) = symbols r1 ++ symbols r2
symbols (Star r) = symbols r
symbols (Plus r) = symbols r
symbols (Group r) = symbols r


-- Choose only unique symbols in regular expression
uniqueSymbols r = map head (group (sort (symbols r)))


indexInRE i c (Epsilon) = []
indexInRE i c (Ch a)
  | a == c    = [i]
  | otherwise = []
indexInRE i c (Any) = [i]
indexInRE i c (Option r) = indexInRE i c r
indexInRE i c (Seq r1 r2) = indexInRE i c r1 ++ indexInRE (i + countCh r1) c r2
indexInRE i c (Alt r1 r2) = indexInRE i c r1 ++ indexInRE (i + countCh r1) c r2
indexInRE i c (Star r) = indexInRE i c r
indexInRE i c (Plus r) = indexInRE i c r
indexInRE i c (Group r) = indexInRE i c r


indexOf c r = indexInRE 1 c r


-- Convert array of positions of binary bits to decimal number
--   numState [1, 2, 5] = 38
numState [] = 0
numState (i:arr) = (2 ^ i) + numState(arr)


-- Convert integer to positions of binary 1
--   38 = [0,1,0,0,1,1,0]
posState 0 = [0]
posState i = posState(i `div` 2) ++ (i `mod` 2) : []


-- Bit set represents Table B in the assignment
bitSetPositions regex [] = []
bitSetPositions regex (i:arr)
  | not (null arr)  = bitSetPositions regex arr ++ (i, (indexOf (i !! 0) regex)) : []
  | otherwise       = (i, (indexOf (i !! 0) regex)) : []


bitSet [] = []
bitSet (i:arr) = bitSet(arr) ++ (fst i, numState (snd i)) : []


-- Retrieve bit state associated with a character
bitStateFor c [] = 0
bitStateFor c (el:set)
  | c == (fst el) !! 0 = (snd el)
  | otherwise          = bitStateFor c set


-- Bit set represents Table D in the assignment
-- Entry (0, 2) means that possible transitions from state 0 are 0b10 (only the first symbol)
transitionSet r = sort ((0, numState(firstSym(r))) : generateTransitionSet(groupedTransitionSets(pairSym(r))))


generateTransitionSet [] = []
generateTransitionSet (el:group) = generateTransitionSet(group) ++ (fst el, numState (snd el)) : []


allTransitionSets (allPairs) [] = []
allTransitionSets (allPairs) (p:pairs) = allTransitionSets allPairs pairs ++ (p !! 0, transitionSetEntryFor (p !! 0) allPairs) : []
groupedTransitionSets (allPairs) = map head (group (sort (allTransitionSets (allPairs) (allPairs))))


transitionSetEntryFor i [] = []
transitionSetEntryFor i (p:pairs)
  | i == (p !! 0)  = transitionSetEntryFor i pairs ++ (p !! 1) : []
  | otherwise      = transitionSetEntryFor i pairs


transitionStateFor i [] = 0
transitionStateFor i (el:set)
  | i == (fst el) = (snd el)
  | otherwise     = transitionStateFor i set


-- Determines value of next state
-- E.g., If (D[s] 'LOGIC AND' B[c]) = 010100, then 'LOGIC OR' all transitions possible from 2 and 4
transitionsFrom [] set = 0
transitionsFrom (i:arr) set
  | i /= 0    = transitionsFrom arr set .|. transitionStateFor (i * length(arr)) set
  | otherwise = transitionsFrom arr set


match (Epsilon) s = s == ""
match (Ch c) "" = False
match (Ch c) (s:r) = s == c && r == []
match (Any) "" = False
match (Any) (s:r) = r == []
match (Option o) "" = True
match (Option o) s = match o s
match (Alt r1 r2) s = (match r1 (take (countCh r1) s) || match r2 (drop (countCh r2) s)) || (_match (Alt r1 r2) s)
match (Seq r1 r2) s = (match r1 (take (countCh r1) s) && match r2 (drop (countCh r2) s)) || (_match (Seq r1 r2) s)
match (Star Any) s = True
match (Star r) "" = True
match (Star r) s
  | match r (take 1 s)  = match (Star r) (drop 1 s)
  | otherwise           = _match (Star r) s
match (Plus r) "" = False
match (Plus Any) s = s /= ""
match (Plus r) s
  | match r (take 1 s)  = match (Plus r) (drop 1 s)
  | otherwise           = _match (Plus r) s
match (Group r) s = match r s


-- Starts matching using Gluskov's Algorithm
--  r      - Regular Expression
--  str    - String to match
--  istate - Initial state S_0 = 1
--  fstate - Final state F, e.g. 101000 where bits correspond to last symbols of r
--  bset   - Bit set B, e.g. [("a", 100010), ("b", 011100)]
--  tset   - Transition set T, e.g. [(0,10=0b001010),(1,4),(3,16),(4,8)]
_match r str = glushkovMatch (str) (istate) (fstate r) (bset r) (tset r)


-- Match Using Glushkov's Algorithm
glushkovMatch [] state fin bit trans = False
glushkovMatch (c:str) state fin bit trans
  | null str  = (nextState c state bit trans) .&. fin /= 0
  | otherwise = (glushkovMatch str (nextState c state bit trans) fin bit trans)


-- Determine next state
nextState c s b t = (transitionsFrom (posState s) t) .&. (bitStateFor c b)


-- Initial State
istate = (1)


-- Create Bit Set which indicates which states can be reached from current state
-- Type [("a", 2), (...)]
bset r = bitSet ((bitSetPositions r) (uniqueSymbols r))


-- Create Final State based on last symbols' positions
fstate r = numState (lastSym r)


-- Create Transition Set, e.g. [(5, 16), (...)], where 5 is a state and 16 = 0b10000
tset r = transitionSet r





-- 3.  A parser to convert text into regular expressions

-- text_match "(ab*|c)+" "aaaac" = True
text_match r str = case (parseMain r) of
  Just (r) -> (match r str)
  _ -> False

parseRE :: [Char] -> Maybe (RE, [Char])
parseSeq :: [Char] -> Maybe (RE, [Char])
parseItem :: [Char] -> Maybe (RE, [Char])
parseElement :: [Char] -> Maybe (RE, [Char])
parseChar :: [Char] -> Maybe (RE, [Char])
parseMain :: [Char] -> Maybe RE

parseChar [] = Nothing
parseChar (c:s)
  | c == '|' || c == '*' || c == '(' || c == ')' || c == '?' || c == '+' || c == '\\' = Nothing
  | c == '.'                                                             = Just ((Any), s)
  | otherwise                                                            = Just ((Ch c), s)

parseElement ('(':more) =
    case parseRE(more) of
        Just (re, ')':yet_more) -> Just(Group re, yet_more)
        _ -> Nothing

parseElement ('\\':more) =
    case parseChar(more) of
        Just (re, yet_more) -> Nothing
        _ -> Just ((Ch ((more !! 0))), (drop 1 more))
parseElement s = parseChar s

parseItem s =
   case parseElement(s) of
        Just (re, '*':more) -> Just (Star re, more)
        Just (re, '+':more) -> Just (Plus re, more)
        Just (re, '?':more) -> Just (Option re, more)
        Just (re, more) -> Just (re, more)
        _ -> Nothing

extendSeq :: (RE, [Char]) -> Maybe (RE, [Char])

parseSeq s =
    case parseItem(s) of
        Just (r, more_chars) -> extendSeq(r, more_chars)
        _ -> Nothing

extendSeq (e1, after1) =
    case parseItem(after1) of
        Just(e2, more) -> extendSeq(Seq e1 e2, more)
        _ -> Just(e1, after1)

extendRE :: (RE, [Char]) -> Maybe (RE, [Char])
parseRE s =
    case parseSeq(s) of
        Just (r, more_chars) -> extendRE(r, more_chars)
        _ -> Nothing

extendRE (e1, []) = Just (e1, [])
extendRE (e1, '|' : after_bar) =
    case parseSeq(after_bar) of
        Just(e2, more) -> extendRE(Alt e1 e2, more)
        _ -> Nothing
extendRE(e1, c:more) = Just (e1, c:more)

parseMain s = case parseRE s of
    Just (e, []) -> Just e
    _ -> Nothing







-- 4.  Searching for matching lines in a file


extendedRE :: RE -> RE
matches :: RE -> [[Char]] -> [[Char]]
searches :: RE -> [[Char]] -> [[Char]]
search :: RE -> [Char] -> Bool
matching :: [Char] -> [[Char]] -> [[Char]]


matches re lines = filter (match re) lines


searches re lines = filter (search re) lines


extendedRE re = Seq (re) (Star Any)


-- Search for "Line.*"
search re [] = False
search re line
  | match (extendedRE re) line   = True
  | otherwise                    = search re (drop 1 line)


matching regexp lines = case parseMain regexp of
                            Just r -> searches r lines
                            _ -> []





-- 5.  Command line interface

main = do
  [regExp, fileName] <- getArgs
  srcText <- readFile fileName
  hPutStr stdout (unlines (matching regExp (lines srcText)))
