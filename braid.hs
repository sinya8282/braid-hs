-- Author: Ryoma Sin'ya
-- This program is an implementation of
-- "Algorithms for positive braids".

import Data.List
import Control.Monad
import Control.Applicative
import Debug.Trace

type Rank = Int
type Element = Int
data Braid = Braid { rank :: Rank, elements :: [Element] } deriving (Eq, Show)
type PositiveBraid = Braid
type PositivePermutationBraid = PositiveBraid
type Permutation = [Element]

validate :: Rank -> Int -> Element
validate r b = if abs b < r then b else 0

generator :: Rank -> Int -> Braid
generator r b = Braid r $ [validate r b]

fromList :: [Element] -> Braid
fromList l = Braid rank' l
    where
      rank' = (+1) . maximum $ map (abs) l

fromStr :: String -> Braid
fromStr = fromList . (map read) . words

transform :: ([Element] -> [Element]) -> Braid -> Braid
transform f b = Braid (rank b) $ f $ elements b

resize :: Rank -> Braid -> Braid
resize r b = Braid r $ map (validate r) $ elements b

-- basic functions

infix 6 $+
($+) :: Braid -> Braid -> Braid
a $+ b = Braid (rank b) $ elements a ++ elements b

infix 7 $*
($*) :: Braid -> Braid -> Braid
a@(Braid r (i:_)) $* b@(Braid _ (j:_))
    | i == j = Braid r [i]
    | abs (i - j) == 1 = Braid r [i,j,i]
    | otherwise = Braid r [i,j]

infix 8 $^
($^) :: Braid -> Int -> Braid
b $^ n
    | n >= 0 = transform (concat . replicate n) b
    | otherwise = inverse $ b $^ (-n)

fundamentalBraid :: Rank -> Braid
fundamentalBraid n = (Braid n $ enum n)
    where
      enum 1 = [0]
      enum 2 = [1]
      enum n = enum (n - 1) ++ [n-1,n-2..1]

inverse :: Braid -> Braid
inverse = transform $ reverse . map negate

wt :: Braid -> Int
wt = sum . (map wt') . elements
    where
      wt' 0 = 0
      wt' σ = if σ > 0 then 1 else -1

rev :: Braid -> Braid
rev = transform $ reverse

τ :: Braid -> Braid
τ b = transform (map tau') b
    where
      tau' 0 = 0
      tau' n = (sign n *) $ (rank b -) $ abs n
      sign n = if (n >= 0) then 1 else -1

-- permutaion functions

permute :: [Int] -> Permutation -> [Int]
permute xs p = map (\i -> xs !! (i-1)) p

permutation :: Rank -> Element -> Permutation
permutation r σ = [1..σ-1] ++ [σ+1, σ] ++ [σ+2..r]

fromPermutation :: Permutation -> PositivePermutationBraid
fromPermutation p = Braid len $ perm p
    where
      len = length p
      perm [] = []
      perm (1:xs) = perm (map (subtract 1) xs)
      perm xs = gen (elemIndex 1 xs) (len - (length xs)) ++
                perm (map (subtract 1) $ xs \\ [1])
      gen (Just i) j = map (+ j) $ reverse [1..i]

toPermutation :: PositivePermutationBraid -> Permutation
toPermutation b = foldr permute [1..r] $ map (permutation r) $ elements b
    where
      r = rank b

inversePermutation :: Permutation -> Permutation
inversePermutation p = map ((\(Just i) -> i+1) . (`elemIndex` p)) [1..length p]

startingSet :: Permutation -> [Element]
startingSet p = filter (/= 0) $ zipWith (\i (x, x') -> if x > x' then i else 0) [1..] $ zip p $ tail p

finishingSet :: Permutation -> [Element]
finishingSet p = startingSet $ inversePermutation p

factorialCoordinate :: Permutation -> Int
factorialCoordinate p = sum $ zipWith (*) coefficients crosses
    where
      coefficients = map factorial [0..(length p)-1]
      crosses = [1..(length p)]

factorial :: Int -> Int
factorial 0 = 1
factorial n = n * factorial (n - 1)

-- This is main algorithm for word problem (equivalence check)
-- based on a Braid's "canonical form".
-- reference: Morton & Elrifai, "Algorithms for positive braids"
infix 4 $==
($==) :: Braid -> Braid -> Bool
a $== b = canonicalForm a == canonicalForm b

canonicalForm :: Braid -> (Int, [PositiveBraid])
canonicalForm b = (pow, fac)
    where
      (pow, pb) = reform b
      fac = leftCanonicalForm pb

reform :: Braid -> (Int, PositiveBraid)
reform b = foldl order (0, Braid r []) $ elements b
    where
      r = rank b
      order (pow, pb) σ
          | σ > 0 = (pow, pb $+ generator r σ)
          | otherwise = (pow-1, τ(pb) $+ rewrite σ)
      rewrite σ = fromPermutation $ permute residual fundamentalPerm
          where
            fundamentalPerm = toPermutation $ fundamentalBraid r
            residual = permutation r (-σ)

-- Theorem 2.9: There is a unique expression for P ≥ e as P = A1A2 ···Ak
--                with Ai ∈ [0,1], Ak ≠ e and S(Ai+1) ⊂ F(Ai) for each i.
leftCanonicalForm :: PositiveBraid -> [PositiveBraid]
leftCanonicalForm pb = map fromPermutation $ lcf [] $ map (permutation r) $ elements pb
    where
      r = rank pb

      lcf fac' fac
          | fac' == fac = fac
          | otherwise = lcf fac $ fst $ foldr order ([], []) $ zip (fundamentalPerm:fac) fac
      fundamentalPerm = toPermutation $ fundamentalBraid r
      order (a, b) (acc, carry) = order' $ finishingSet a \\ startingSet b
          where
            b' = permute b carry
            order' [] = (b':acc, [])
            order' carry' = (b':acc, carry')


fromCanonicalForm :: (Int, [PositiveBraid]) -> Braid
fromCanonicalForm (pow, fac) = foldl ($+) pf fac
    where
      pf = (fundamentalBraid $ rank $ head $ fac) $^ pow

reduce :: Braid -> Braid
reduce b = Braid (rank b) $ reduce' [] $ filter (/= 0) (elements b)
    where
      reduce' e e'
          | length e == length e' = e'
          | otherwise = reduce' e' $ reduce'' e'
      reduce'' [] = []
      reduce'' xs@(x:[]) = xs
      reduce'' (x:xs@(y:ys))
          | x + y == 0 = reduce'' ys
          | otherwise = x : reduce'' xs

inf :: Braid -> Int
inf b = fst $ canonicalForm b

sup :: Braid -> Int
sup b = (\(f, s) -> f + length s) $ canonicalForm b

ℓ  :: Braid -> Int
ℓ  b = length . snd $ canonicalForm b

-- REPL

main = forever $ do
  putStr $! "braid: "
  braid' <- getLine
  putStrLn . toAA . fromStr $ braid'

p = putStrLn.toAA

toAA :: Braid -> String
toAA b = edge ++ foldl (pretty (rank b)) "\n" (elements b) ++ edge
    where
      pretty r s 0 = s
      pretty r s g = s ++ concatMap ((space ++) . pretty' r (abs g) 1) (crossStr g)
      pretty' r g i s
          | i > r  = "\n"
          | g == i = s ++ space ++ pretty' r g (i + 2) s
          | otherwise = "｜" ++ space ++ pretty' r g (i + 1) s
      space = "　　"
      edge = space ++ (concatMap (: space) $ concat $ replicate (rank b) "｜")
      crossStr g = if g > 0 then [" ＼　／ ",
                                  " 　／　 ",
                                  " ／　＼ "]
                            else [" ＼　／ ",
                                  " 　＼　 ",
                                  " ／　＼ "]