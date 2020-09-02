--
-- Maxim Puchkov
-- 301314335
-- CMPT 384 Assignment 1A
--
-- Regular Expressions in Haskell
-- Using Glushkov's Algorithm
--

import System.Environment
import System.IO (stdout,stderr,hPutStr,hPutStrLn)
import Data.Bits
import Data.List
import Data.Char
import Data.Array


-- 1. An algebraic data type for regular expressions

data RE = Epsilon | Any | Ch Bool [Char] | Seq RE RE | Alt RE RE
          | Star RE | Plus RE | Group RE deriving Show





-- Positions of characters

countCh Epsilon = 0
countCh (Ch p c) = 1
countCh (Any) = 1
countCh (Seq r1 r2) = (countCh r1) + (countCh r2)
countCh (Alt r1 r2) = (countCh r1) + (countCh r2)
countCh (Star r) = countCh r
countCh (Plus r) = countCh r
countCh (Group r) = countCh r

matchesEmpty Epsilon = True
matchesEmpty (Ch p c) = False
matchesEmpty (Any) = True
matchesEmpty (Seq r1 r2) = (matchesEmpty r1) && (matchesEmpty r2)
matchesEmpty (Alt r1 r2) = (matchesEmpty r1) || (matchesEmpty r2)
matchesEmpty (Star r) = True
matchesEmpty (Plus r) = False
matchesEmpty (Group r) = matchesEmpty r

firstWithIndex i Epsilon = []
firstWithIndex i (Ch p c) = [i]
firstWithIndex i (Any) = [i]
firstWithIndex i (Seq r1 r2)
   | matchesEmpty r1 = (firstWithIndex i r1) ++ (firstWithIndex (i + countCh r1) r2)
   | otherwise       = (firstWithIndex i r1)
firstWithIndex i (Alt r1 r2) = (firstWithIndex i r1) ++ (firstWithIndex (i + countCh r1) r2)
firstWithIndex i (Star r) = firstWithIndex i r
firstWithIndex i (Plus r) = firstWithIndex i r
firstWithIndex i (Group r) = firstWithIndex i r

firstSyms r = firstWithIndex 1 r

finals_ix i Epsilon = []
finals_ix i (Ch p c) = [i]
finals_ix i (Any) = [i]
finals_ix i (Seq r1 r2)
   | matchesEmpty r2 = (finals_ix i r1) ++ (finals_ix (i + countCh r1) r2)
   | otherwise       = finals_ix (i + countCh r1) r2
finals_ix i (Alt r1 r2) = (finals_ix i r1) ++ (finals_ix (i + countCh r1) r2)
finals_ix i (Star r) = finals_ix i r
finals_ix i (Plus r) = finals_ix i r
finals_ix i (Group r) = finals_ix i r

finalSyms r = finals_ix 1 r

pairs_ix i Epsilon = []
pairs_ix i (Ch p c) = []
pairs_ix i (Any) = []
pairs_ix i (Seq r1 r2) =
   let i2 = i + countCh r1 in
   (pairs_ix i r1) ++ (pairs_ix i2 r2) ++ all_pairs (finals_ix i r1) (firstWithIndex i2 r2)
pairs_ix i (Alt r1 r2) = (pairs_ix i r1) ++ (pairs_ix (i + countCh r1) r2)
pairs_ix i (Star r) = (pairs_ix i r) ++ all_pairs (finals_ix i r) (firstWithIndex i r)
pairs_ix i (Plus r) = (pairs_ix i r) ++ all_pairs (finals_ix i r) (firstWithIndex i r)
pairs_ix i (Group r) = pairs_ix i r

all_pairs list1 list2 = [(e1, e2) | e1 <- list1, e2 <- list2]

symPairs r = pairs_ix 1 r






-- Computing the tables


position_vec :: [Int] -> Int
position_vec posns = foldr (.|.) 0 (map (2^) posns)

compareToAll :: Char -> [Char] -> Bool
compareToAll c [] = False
compareToAll c (ch:str) = (ch == c) .|. (compareToAll c str)

ch_positions :: Char -> Int -> RE -> [Int]
ch_positions c i Epsilon = []
ch_positions c i (Ch p (c0:more))
    | p && c == c0                            = [i]
    | p && more /= []                         = ch_positions c i (Ch p more)
    | not p && not (compareToAll c (c0:more)) = [i]
    | otherwise                               = []
ch_positions c i (Any) = [i]
ch_positions c i (Seq r1 r2) = (ch_positions c i r1) ++ (ch_positions c (i + countCh r1) r2)
ch_positions c i (Alt r1 r2) = (ch_positions c i r1) ++ (ch_positions c (i + countCh r1) r2)
ch_positions c i (Star r) = (ch_positions c i r)
ch_positions c i (Plus r) = (ch_positions c i r)
ch_positions c i (Group r) = (ch_positions c i r)


tableB r = listArray (0, 127) [position_vec (ch_positions (chr c) 1 r) | c <- [0..127]]


transition_vec :: Int -> Int -> [(Int, Int)] -> Int
transition_vec initial_vec state_vec []
    | (state_vec .&. 1) > 0 = initial_vec
    | otherwise           = 0
transition_vec initial_vec state_vec ((s, t) : more)
    | 2^s .&. state_vec > 0  = 2^t .|. (transition_vec initial_vec state_vec more)
    | otherwise     = transition_vec initial_vec state_vec more


tableD :: RE -> Array Int Int
tableD r =
    let initialVec = position_vec (firstSyms r)
        pairs = symPairs r
        stateMax = 2^(1 + countCh r) - 1 in
    listArray (0, stateMax) [transition_vec initialVec s pairs | s <- [0..stateMax]]


vectorF :: RE -> Int
vectorF r
    | matchesEmpty r  = position_vec (0: (finalSyms r))
    | otherwise       = position_vec (finalSyms r)


-- Matching

match_NFA :: Int -> (Array Int Int, Array Int Int, Int) -> [Char] -> Bool
match_NFA s (b, d, f) [] = (s .&. f) > 0
match_NFA s (b, d, f) (ch:more) = match_NFA ((b!(ord ch)) .&. (d!s)) (b, d, f) more

match r string = match_NFA 1 (tableB r, tableD r, vectorF r) string

-- Searching

tableB_search r = listArray (0, 127) [position_vec (ch_positions (chr c) 1 r) .|. 1| c <- [0..127]]

tableD_search r =
    let initialVec = position_vec (firstSyms r)
        pairs = symPairs r
        stateMax = 2^(1 + countCh r) - 1 in
    listArray (0, stateMax) [(transition_vec initialVec s pairs .|. 1) | s <- [0..stateMax]]

search_NFA :: Int -> (Array Int Int, Array Int Int, Int) -> [Char] -> Bool
search_NFA s (b, d, f) [] = (s .&. f) > 0
search_NFA s (b, d, f) (ch:more)
    | (s .&. f) > 0    = True
    | otherwise        = search_NFA ((b!(ord ch)) .&. (d!s) .|. 1) (b, d, f) more

search r string = search_NFA 1 (tableB_search r, tableD_search r, vectorF r) string











-- 3.  A parser to convert text into regular expressions


text_match r str = case (parseMain r) of
  Just (r) -> (match r str)
  _ -> False

text_search r str = case (parseMain r) of
  Just (r) -> (search r str)
  _ -> False

regex r = case (parseMain r) of
  Just (r) -> r
  _ -> Epsilon

parseRE :: [Char] -> Maybe (RE, [Char])
parseSeq :: [Char] -> Maybe (RE, [Char])
parseItem :: [Char] -> Maybe (RE, [Char])
parseElement :: [Char] -> Maybe (RE, [Char])
parseChar :: [Char] -> Maybe (RE, [Char])
parseMain :: [Char] -> Maybe RE

parseChar [] = Nothing
parseChar ('\\':c:s)
  | isMetachar c                                   = Just ((Ch True [c]), s)
  | otherwise                                      = Nothing
parseChar ('[':'^':more) =
   case parseClassItems(more) of
        Just (chars, ']':more) -> Just (Ch False chars, more)
        _ -> Nothing
parseChar ('[':more) =
   case parseClassItems(more) of
        Just (chars, ']':more) -> Just (Ch True chars, more)
        _ -> Nothing
parseChar (c:s)
  | isMetachar c                                   = Nothing
  | otherwise                                      = Just ((Ch True [c]), s)

classLastIndex s =
  case findIndex (==']') s of
    Just(n) -> n
    _ -> length(s)

setLastIndex s =
  case findIndex (=='-') s of
    Just(n) -> n
    _ -> 0

rangeOfCharacters :: Char -> Char -> [Char]
rangeOfCharacters ci cf =
  [chr e | e <- [ord ci .. ord cf]]


parseClassItems :: [Char] -> Maybe([Char], [Char])
parseClassItems [] = Nothing
parseClassItems s =
  let i = classLastIndex s
      j = setLastIndex s
      subs = take i s
      ci = (drop (j - 1) (take j subs))!!0
      cf = (take 1 (drop (j + 1) subs))!!0
      more = drop i s
      in
        if (j == 0) then
          Just([e | e <- subs], more)
        else
          Just(rangeOfCharacters ci cf, more)

isMetachar c = elem c "|*()\\.?+["

parseElement ('.':more) = Just (Any, more)
parseElement ('(':more) =
    case parseRE(more) of
        Just (re, ')':yet_more) -> Just(Group re, yet_more)
        _ -> Nothing
parseElement s = parseChar s

parseItem s =
   case parseElement(s) of
        Just (re, '*':more) -> Just (Star re, more)
        Just (re, '?':more) -> Just (Alt re Epsilon, more)
        Just (re, '+':more) -> Just (Plus re, more)
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











-- Matching & Searching the file

matches :: RE -> [[Char]] -> [[Char]]
matching :: [Char] -> [[Char]] -> [[Char]]
searches :: RE -> [[Char]] -> [[Char]]
searching :: [Char] -> [[Char]] -> [[Char]]

matches re lines = filter (match re) lines

matching regexp lines = case parseMain regexp of
                            Just r -> matches r lines
                            _ -> []

searches re lines = filter (search re) lines

searching regexp lines = case parseMain regexp of
                            Just r -> searches r lines
                            _ -> []




-- 5.  Command line interface

main = do
  [regExp, fileName] <- getArgs
  srcText <- readFile fileName
  hPutStr stdout (unlines (matching regExp (lines srcText)))
