------------------------- Auxiliary functions

merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x : xs) (y : ys)
  | x == y = x : merge xs ys
  | x <= y = x : merge xs (y : ys)
  | otherwise = y : merge (x : xs) ys

minus :: Ord a => [a] -> [a] -> [a]
minus xs [] = xs
minus [] ys = []
minus (x : xs) (y : ys)
  | x < y = x : minus xs (y : ys)
  | x == y = minus xs ys
  | otherwise = minus (x : xs) ys

variables :: [Var]
variables = [[x] | x <- ['a' .. 'z']] ++ [x : show i | i <- [1 ..], x <- ['a' .. 'z']]

removeAll :: [Var] -> [Var] -> [Var]
removeAll xs ys = [x | x <- xs, not (elem x ys)]

fresh :: [Var] -> Var
fresh = head . removeAll variables

-- - - - - - - - - - - -- Terms

type Var = String

data Term
  = Variable Var
  | Lambda Var Term
  | Apply Term Term

pretty :: Term -> String
pretty = f 0
  where
    f i (Variable x) = x
    f i (Lambda x m) = if elem i [2, 3] then "(" ++ s ++ ")" else s where s = "\\" ++ x ++ ". " ++ f 1 m
    f i (Apply m n) = if elem i [3] then "(" ++ s ++ ")" else s where s = f 2 m ++ " " ++ f 3 n

instance Show Term where
  show = pretty

-- - - - - - - - - - - -- Numerals

numeral :: Int -> Term
numeral i = Lambda "f" (Lambda "x" (numeral' i))
  where
    numeral' i
      | i <= 0 = Variable "x"
      | otherwise = Apply (Variable "f") (numeral' (i - 1))

-- - - - - - - - - - - -- Renaming, substitution, beta-reduction

used :: Term -> [Var]
used (Variable x) = [x]
used (Lambda x m) = [x] `merge` used m
used (Apply m n) = used n `merge` used m

rename :: Var -> Var -> Term -> Term
rename y z (Variable x)
  | y == x = Variable z
  | otherwise = Variable x
rename y z (Lambda x m)
  | y == x = Lambda x m
  | otherwise = Lambda x (rename y z m)
rename y z (Apply m n) = Apply (rename y z m) (rename y z n)

substitute :: Var -> Term -> Term -> Term
substitute y p (Variable x)
  | y == x = p
  | otherwise = Variable x
substitute y p (Lambda x m)
  | y == x = Lambda x m
  | otherwise = Lambda z (substitute y p (rename x z m))
  where
    z = fresh (used p `merge` used m `merge` [x, y])
substitute y p (Apply m n) = Apply (substitute y p m) (substitute y p n)

beta :: Term -> [Term]
beta (Apply (Lambda x m) n) =
  [substitute x n m]
    ++ [Apply (Lambda x m') n | m' <- beta m]
    ++ [Apply (Lambda x m) n' | n' <- beta n]
beta (Variable _) = []
beta (Lambda x m) = [Lambda x m' | m' <- beta m]
beta (Apply m n) =
  [Apply m' n | m' <- beta m]
    ++ [Apply m n' | n' <- beta n]

-- - - - - - - - - - - -- Normalize

normalize :: Term -> IO ()
normalize m = do
  print m
  let ms = beta m
  if null ms
    then return ()
    else normalize (head ms)

------------------------- Assignment 1: Combinators

infixl 5 :@

data Combinator = I | K | S | B | C | Q | R | X | Y | Z | Combinator :@ Combinator | V String

example1 :: Combinator
example1 = S :@ K :@ K :@ V "x"

example2 :: Combinator
example2 = S :@ (K :@ K) :@ I :@ V "x" :@ V "y"

-- - - - - - - - - - - -- show, parse

instance Show Combinator where
  show = f 0
    where
      f _ I = "I"
      f _ K = "K"
      f _ S = "S"
      f _ B = "B"
      f _ C = "C"
      f _ Q = "Q"
      f _ R = "R"
      f _ X = "X"
      f _ Y = "Y"
      f _ Z = "Z"
      f _ (V s) = s
      f i (c :@ d) = if i == 1 then "(" ++ s ++ ")" else s where s = f 0 c ++ " " ++ f 1 d

parse :: String -> Combinator
parse s = down [] s
  where
    down :: [Maybe Combinator] -> String -> Combinator
    down cs (' ' : str) = down cs str
    down cs ('(' : str) = down (Nothing : cs) str
    down cs ('I' : str) = up cs I str
    down cs ('K' : str) = up cs K str
    down cs ('S' : str) = up cs S str
    down cs ('B' : str) = up cs I str
    down cs ('C' : str) = up cs I str
    down cs ('Q' : str) = up cs I str
    down cs ('R' : str) = up cs I str
    down cs ('X' : str) = up cs I str
    down cs ('Y' : str) = up cs I str
    down cs ('Z' : str) = up cs I str
    down cs (c : str) = up cs (V [c]) str
    up :: [Maybe Combinator] -> Combinator -> String -> Combinator
    up [] c [] = c
    up (Just c : cs) d str = up cs (c :@ d) str
    up (Nothing : cs) d (')' : str) = up cs d str
    up cs d str = down (Just d : cs) str

-- - - - - - - - - - - -- step, run

step :: Combinator -> [Combinator]
step (V _) = []
step I = []
step K = []
step S = []
step B = []
step C = []
step Q = []
step R = []
step X = []
step Y = []
step Z = []
step (I :@ x) = x : [I :@ x' | x' <- step x]
step (K :@ x :@ y) =
  x
    : [K :@ x' :@ y | x' <- step x]
    ++ [K :@ x :@ y' | y' <- step y]
step (S :@ x :@ y :@ z) =
  (x :@ z :@ (y :@ z))
    : [S :@ x' :@ y :@ z | x' <- step x]
    ++ [S :@ x :@ y' :@ z | y' <- step y]
    ++ [S :@ x :@ y :@ z' | z' <- step z]
step (B :@ x :@ y :@ z) =
  (x :@ (y :@ z))
    : [B :@ x' :@ y :@ z | x' <- step x]
    ++ [B :@ x :@ y' :@ z | y' <- step y]
    ++ [B :@ x :@ y :@ z' | z' <- step z]
step (C :@ x :@ y :@ z) =
  ((x :@ z) :@ y)
    : [C :@ x' :@ y :@ z | x' <- step x]
    ++ [C :@ x :@ y' :@ z | y' <- step y]
    ++ [C :@ x :@ y :@ z' | z' <- step z]
step (Q :@ u :@ x :@ y) =
  (u :@ x)
    : [Q :@ u' :@ x :@ y | u' <- step u]
    ++ [Q :@ u :@ x' :@ y | x' <- step x]
    ++ [Q :@ u :@ y :@ y' | y' <- step y]
step (R :@ u :@ v :@ x :@ y) =
  (u :@ v :@ x)
    : [R :@ u' :@ v :@ x :@ y | u' <- step u]
    ++ [R :@ u :@ v' :@ x :@ y | v' <- step v]
    ++ [R :@ u :@ v :@ x' :@ y | x' <- step x]
    ++ [R :@ u :@ v :@ x :@ y' | y' <- step y]
step (X :@ u :@ x :@ y :@ z) =
  (u :@ x :@ (y :@ z))
    : [X :@ u' :@ x :@ y :@ z | u' <- step u]
    ++ [X :@ u :@ x' :@ y :@ z | x' <- step x]
    ++ [X :@ u :@ y :@ y' :@ z | y' <- step y]
    ++ [X :@ u :@ y :@ y :@ z' | z' <- step z]
step (Y :@ u :@ x :@ y :@ z) =
  (u :@ (x :@ z) :@ y)
    : [Y :@ u' :@ x :@ y :@ z | u' <- step u]
    ++ [Y :@ u :@ x' :@ y :@ z | x' <- step x]
    ++ [Y :@ u :@ y :@ y' :@ z | y' <- step y]
    ++ [Y :@ u :@ y :@ y :@ z' | z' <- step z]
step (Z :@ u :@ x :@ y :@ z) =
  (u :@ (x :@ z) :@ (y :@ z))
    : [Z :@ u' :@ x :@ y :@ z | u' <- step u]
    ++ [Z :@ u :@ x' :@ y :@ z | x' <- step x]
    ++ [Z :@ u :@ y :@ y' :@ z | y' <- step y]
    ++ [Z :@ u :@ y :@ y :@ z' | z' <- step z]
step (x :@ y) =
  [x' :@ y | x' <- step x]
    ++ [x :@ y' | y' <- step y]

run :: Combinator -> IO ()
run x = do
  print x
  let xs = step x
  if null xs
    then return ()
    else run (head xs)

------------------------- Assignment 2: Combinators to Lambda-terms

toLambda :: Combinator -> Term
toLambda (c :@ d) = Apply (toLambda c) (toLambda d)
toLambda I = Lambda "x" (Variable "x")
toLambda K = Lambda "x" (Lambda "y" (Variable "x"))
toLambda S = Lambda "x" (Lambda "y" (Lambda "z" (Apply (Apply (Variable "x") (Variable "z")) (Apply (Variable "y") (Variable "z")))))
toLambda B = Lambda "x" (Lambda "y" (Lambda "z" (Apply (Variable "x") (Apply (Variable "y") (Variable "z")))))
toLambda C = Lambda "x" (Lambda "y" (Lambda "z" (Apply (Apply (Variable "x") (Variable "z")) (Variable "y"))))
toLambda Q = Lambda "u" (Lambda "x" (Lambda "y" (Apply (Variable "u") (Variable "x"))))
toLambda R = Lambda "u" (Lambda "v" (Lambda "x" (Lambda "y" (Apply (Apply (Variable "u") (Variable "v")) (Variable "x")))))
toLambda X = Lambda "u" (Lambda "x" (Lambda "y" (Lambda "z" (Apply (Apply (Variable "u") (Variable "x")) (Apply (Variable "y") (Variable "z"))))))
toLambda Y = Lambda "u" (Lambda "x" (Lambda "y" (Lambda "z" (Apply (Apply (Variable "u") (Apply (Variable "x") (Variable "z"))) (Variable "y")))))
toLambda Z = Lambda "u" (Lambda "x" (Lambda "y" (Lambda "z" (Apply (Apply (Variable "u") (Apply (Variable "x") (Variable "z"))) (Apply (Variable "y") (Variable "z"))))))
toLambda (V x) = Variable x

------------------------- Assignment 3: Lambda-terms to Combinators

abstract :: Var -> Combinator -> Combinator
abstract x (V c)
  | x == c = I
  | otherwise = K :@ V c
abstract x I = K :@ I
abstract x K = K :@ K
abstract x S = K :@ S
abstract x (c :@ d) = S :@ abstract x c :@ abstract x d

toCombinator :: Term -> Combinator
toCombinator (Variable x) = V x
toCombinator (Lambda x m) = abstract x (toCombinator m)
toCombinator (Apply m n) = toCombinator m :@ toCombinator n

------------------------- Assignment 4: Estimating growth

sizeL :: Term -> Int
sizeL (Apply m n) = 1 + sizeL m + sizeL n
sizeL (Lambda x m) = 1 + sizeL m
sizeL (Variable x) = 1

sizeC :: Combinator -> Int
sizeC (c :@ d) = 1 + sizeC c + sizeC d
sizeC (V x) = 1
sizeC c = 1

series :: Int -> Term
series n = lambdaPart n n
  where
    lambdaPart :: Int -> Int -> Term
    lambdaPart p q
      | p == 0 = Lambda (variables !! p) (applyPart q)
      | p >= 1 = Lambda (variables !! p) (lambdaPart (p - 1) q)
      | p < 0 = error "Must be at least 0"

    applyPart :: Int -> Term
    applyPart n
      | n > 0 = Apply (applyPart (n - 1)) (Variable (variables !! n))
      | n == 0 = Variable (variables !! n)

------------------------- Assignment 5: Optimised interpretation

data Complexity = Linear | Quadratic | Cubic | Exponential

comb :: Term -> Combinator
comb (Variable x) = V x
comb (Lambda x m) = optimisedAbstract x (comb m)
comb (Apply m n) = comb m :@ comb n

optimisedAbstract :: Var -> Combinator -> Combinator
optimisedAbstract x c
  | not (occurs x c) = K :@ c
  | otherwise = abstractX x c
  where
    abstractX :: Var -> Combinator -> Combinator
    abstractX x (V c)
      | x == c = I
      | otherwise = K :@ V c
    abstractX x (c :@ d :@ e)
      | occurs x d && not (occurs x e) && not (varCheckComb c) = Y :@ c :@ optimisedAbstract x d :@ e
      | occurs x e && not (occurs x d) && not (varCheckComb c) = X :@ c :@ d :@ optimisedAbstract x e
      | occurs x d && occurs x e && not (varCheckComb c) = Z :@ c :@ optimisedAbstract x d :@ optimisedAbstract x e
    abstractX x (c :@ d)
      | occurs x c && not (occurs x d) = C :@ optimisedAbstract x c :@ d
      | occurs x d && not (occurs x c) = B :@ c :@ optimisedAbstract x d
      | otherwise = S :@ optimisedAbstract x c :@ optimisedAbstract x d
    abstractX x c = K :@ c

occurs :: Var -> Combinator -> Bool
occurs x (V c) = c == x
occurs x (c :@ d) = occurs x c || occurs x d
occurs x c = False

varCheckComb :: Combinator -> Bool
varCheckComb (V c) = True
varCheckComb c = False

claim :: Complexity
claim = Cubic
