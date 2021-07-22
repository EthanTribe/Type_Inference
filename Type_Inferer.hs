------------------------- Auxiliary functions

find :: (Show a,Eq a) => a -> [(a,b)] -> b
find x [] = error ("find: " ++ show x ++ " not found")
find x ((y,z):zs)
  | x == y    = z
  | otherwise = find x zs


merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys)
    | x == y    = x : merge xs ys
    | x <= y    = x : merge xs (y:ys)
    | otherwise = y : merge (x:xs) ys

minus :: Ord a => [a] -> [a] -> [a]
minus xs [] = xs
minus [] ys = []
minus (x:xs) (y:ys)
    | x <  y    = x : minus    xs (y:ys)
    | x == y    =     minus    xs    ys
    | otherwise =     minus (x:xs)   ys


------------------------- Lambda-terms

type Var = String

data Term =
    Variable Var
  | Lambda   Var  Term
  | Apply    Term Term
  deriving Eq


instance Show Term where
  show = f 0
    where
      f i (Variable x) = x
      f i (Lambda x m) = if i /= 0 then "(" ++ s ++ ")" else s where s = "\\" ++ x ++ ". " ++ f 0 m 
      f i (Apply  n m) = if i == 2 then "(" ++ s ++ ")" else s where s = f 1 n ++ " " ++ f 2 m

free :: Term -> [Var]
free (Variable x) = [x]
free (Lambda x n) = free n `minus` [x]
free (Apply  n m) = free n `merge` free m


------------------------- Types

infixr 5 :->

type Atom = String
data Type = At Atom | Type :-> Type
  deriving Eq

instance Show Type where
  show (At a)       = a
  show (At a :-> s) = a ++ " -> " ++ show s
  show    (t :-> s) = "(" ++ show t ++ ") -> " ++ show s


atoms :: [Atom]
atoms = map (:[]) ['a'..'z'] ++ [ a : show i | i <- [1..], a <- ['a'..'z'] ]

t1 :: Type
t1 = At "a" :-> At "b"

t2 :: Type
t2 = (At "c" :-> At "d") :-> At "e"

t3 :: Type
t3 = At "a" :-> At "c" :-> At "c"


------------------------- Assignment 1

occurs :: Atom -> Type -> Bool
occurs a (At b)    = a==b
occurs a (t :-> s) = (occurs a t) || (occurs a s)

findAtoms :: Type -> [Atom]
findAtoms (At a)    = [a]
findAtoms (t :-> s) = merge (findAtoms t) (findAtoms s)


------------------------- Type substitution

type Sub = (Atom,Type)

s1 :: Sub
s1 = ("a", At "e")

s2 :: Sub
s2 = ("e", At "b" :-> At "c")

s3 :: Sub
s3 = ("c", At "a" :-> At "a")


------------------------- Assignment 2

sub :: Sub -> Type -> Type
sub s (At a)
  | (fst s) == a = snd s
  | otherwise    = At a
sub s (t :-> r) = (sub s t) :-> (sub s r)

removeLast :: [a] -> [a] -- this function returns the list with the last element removed
removeLast xs = reverse (tail (reverse xs))

subs :: [Sub] -> Type -> Type
subs [] t      = t
subs xs t = subs (removeLast xs) (sub (last xs) t)


------------------------- Unification

type Upair = (Type,Type)
type State = ([Sub],[Upair])

u1 :: Upair
u1 = (t1,At "c")

u2 :: Upair
u2 = (At "a" :-> At "a",At "a" :-> At "c")

u3 :: Upair
u3 = (t1,t2)

u4 :: Upair
u4 = (t2,t3)

st1 :: State
st1 = ([],[u1,u2])


------------------------- Assignment 3

sub_u :: Sub -> [Upair] -> [Upair]
sub_u s []     = []
sub_u s (x:xs) = (sub s (fst x), sub s (snd x)) : (sub_u s xs)

step :: State -> State
step (s, ((At a, At b):xs))
  | a==b      = (s, xs)
  | otherwise = (s ++ [ss], sub_u ss (xs))
    where
      ss :: Sub
      ss = (a, At b)
step (s, ((At a, t):xs))
  | occurs a t = error ("Step: atom " ++ a ++ " occurs in " ++ show t)
  | otherwise  = (s ++ [ss], sub_u ss (xs))
    where
      ss :: Sub
      ss = (a, t)
step (s, ((t, At a):xs))
  | occurs a t = error ("Step: atom " ++ a ++ " occurs in " ++ show t)
  | otherwise  = (s ++ [ss], sub_u ss (xs))
    where
      ss :: Sub
      ss = (a, t)
step (s, ((t:->tt, r:->rr):xs)) = (s, [y] ++ [z] ++ xs)
  where
    y :: Upair
    y = (t,r)
    z :: Upair
    z = (tt,rr)

unify :: [Upair] -> [Sub]
unify u = reverse (steps ([],u))
  where
    steps (s,u)
      | u==[]     = s
      | otherwise = steps (step (s,u))


------------------------- Assignment 4

type Context   = [(Var,Type)]
type Judgement = (Context,Term,Type)

data Derivation = 
    Axiom       Judgement 
  | Abstraction Judgement Derivation
  | Application Judgement Derivation Derivation

n1 = Apply (Lambda "x" (Variable "x")) (Variable "y")



d1 = Application ([("y",At "a")], n1 , At "a") (
       Abstraction ([("y",At "a")],Lambda "x" (Variable "x"),At "a" :-> At "a") (
         Axiom ([("x",At "a"),("y",At "a")],Variable "x",At "a")
     ) ) (
       Axiom ([("y",At "a")], Variable "y", At "a")
     )

d2 = Application ([("y",At "b")],Apply (Lambda "x" (Apply (Variable "x") (Variable "y"))) (Lambda "z" (Variable "z")),At "a") (
       Abstraction ([("y",At "b")],Lambda "x" (Apply (Variable "x") (Variable "y")),At "c") (
         Application ([("x",At "d"),("y",At "b")],Apply (Variable "x") (Variable "y"),At "e") (
           Axiom ([("x",At "d"),("y",At "b")],Variable "x",At "f")
         ) (
           Axiom ([("x",At "d"),("y",At "b")],Variable "y",At "g")
     ) ) ) (
       Abstraction ([("y",At "b")],Lambda "z" (Variable "z"),At "h") (
         Axiom ([("z",At "i"),("y",At "b")],Variable "z",At "j")
     ) )


conclusion :: Derivation -> Judgement
conclusion (Axiom j)            = j 
conclusion (Abstraction j d)    = j 
conclusion (Application j d dd) = j

subs_ctx :: [Sub] -> Context -> Context
subs_ctx [] c = c
subs_ctx xs c = subs_ctx (removeLast xs) (sub_ctx (last xs) c)
  where
    sub_ctx s []     = []
    sub_ctx s (x:xs) = (fst x,(sub s (snd x))) : (sub_ctx s xs)

subs_jdg :: [Sub] -> Judgement -> Judgement
subs_jdg [] j = j
subs_jdg xs j = subs_jdg (removeLast xs) (sub_jdg (last xs) j)
  where
    sub_jdg s (c,trm,typ) = (subs_ctx [s] c, trm, sub s typ)

subs_der :: [Sub] -> Derivation -> Derivation
subs_der xs (Axiom j)            = Axiom (subs_jdg xs j)
subs_der xs (Abstraction j d)    = Abstraction (subs_jdg xs j) (subs_der xs d)
subs_der xs (Application j d dd) = Application (subs_jdg xs j) (subs_der xs d) (subs_der xs dd)


------------------------- Typesetting derivations


instance Show Derivation where
  show d = unlines (reverse strs)
    where
      (_,_,_,strs) = showD d

      showC :: Context -> String
      showC [] = []
      showC [(x,t)]    = x ++ ": " ++ show t
      showC ((x,t):cx) = x ++ ": " ++ show t  ++ " , " ++ showC cx

      showJ :: Judgement -> String
      showJ ([],n,t) =              "|- " ++ show n ++ " : " ++ show t
      showJ (cx,n,t) = showC cx ++ " |- " ++ show n ++ " : " ++ show t

      showL :: Int -> Int -> Int -> String
      showL l m r = replicate l ' ' ++ replicate m '-' ++ replicate r ' '

      showD :: Derivation -> (Int,Int,Int,[String])
      showD (Axiom j) = (0,k,0,[s,showL 0 k 0]) where s = showJ j; k = length s
      showD (Abstraction j d)   = addrule (showJ j) (showD d)
      showD (Application j d e) = addrule (showJ j) (sidebyside (showD d) (showD e))

      addrule :: String -> (Int,Int,Int,[String]) -> (Int,Int,Int,[String])
      addrule x (l,m,r,xs)
        | k <= m     = (ll,k,rr, (replicate ll ' ' ++ x ++ replicate rr ' ') : showL  l m r  : xs)
        | k <= l+m+r = (ll,k,rr, (replicate ll ' ' ++ x ++ replicate rr ' ') : showL ll k rr : xs)
        | otherwise  = (0,k,0, x : replicate k '-' : [ replicate (-ll) ' ' ++ y ++ replicate (-rr) ' ' | y <- xs])
        where
          k = length x
          i = div (m - k) 2
          ll = l+i
          rr = r+m-k-i

      extend :: Int -> [String] -> [String]
      extend i strs = strs ++ repeat (replicate i ' ')

      sidebyside :: (Int,Int,Int,[String]) -> (Int,Int,Int,[String]) -> (Int,Int,Int,[String])
      sidebyside (l1,m1,r1,d1) (l2,m2,r2,d2)
        | length d1 > length d2 = ( l1 , m1+r1+2+l2+m2 , r2 , [ x ++ "  " ++ y | (x,y) <- zip d1 (extend (l2+m2+r2) d2)])
        | otherwise             = ( l1 , m1+r1+2+l2+m2 , r2 , [ x ++ "  " ++ y | (x,y) <- zip (extend (l1+m1+r1) d1) d2])



------------------------- Assignment 5


merge_ctx :: Context -> Context -> Context -- updates/extends a context with a new one
merge_ctx xs []     = xs
merge_ctx xs (y:ys) = merge_ctx (y : (remove_ctx xs y)) ys

remove_ctx :: Context -> (Var,Type) -> Context -- removes a variable type from a context
remove_ctx   []   _ = []
remove_ctx (x:xs) y
    | fst x == fst y = xs
    | otherwise      = x : remove_ctx xs y


derive0 :: Term -> Derivation
derive0 t = aux ([(fv, At "") | fv <- free t], t, At "")
  where
    aux :: Judgement -> Derivation
    aux (c, Variable x, t) = Axiom (c, Variable x, t)
    aux (c, Lambda x n, t) = Abstraction (c, Lambda x n, t) (aux (merge_ctx c [(x,t)], n, t))
    aux (c, Apply n m, t)  = Application (c, Apply n m, t) (aux (c,n,t)) (aux (c,m,t))


everyother :: [a] -> [a] -- returns the elements at even indices of a list
everyother xs = map snd (filter (\x -> odd (fst x)) (numbered xs))
  where
    numbered :: [a] -> [(Int,a)]
    numbered xs = zip [1..] xs

derive1 :: Term -> Derivation
derive1 t = aux (minus atoms [snd x | x <- ("hello", head (minus atoms (free t))) : (zip (free t) (tail (minus atoms (free t))))]) (zip (free t) [At a | a <- tail (minus atoms (free t))], t, At (head (minus atoms (free t))))
  where
    aux :: [Atom] -> Judgement -> Derivation
    aux ts (c, Variable x, t) = Axiom (c, Variable x, t)
    aux ts (c, Lambda x n, t) = Abstraction (c, Lambda x n, t) (aux (drop 2 ts) (merge_ctx c [(x,At (head ts))], n, At (ts!!1)))
    aux ts (c, Apply n m, t)  = Application (c, Apply n m, t) (aux (everyother (drop 2 ts)) (c,n,At (head ts))) (aux (everyother (drop 3 ts)) (c,m,At (ts!!1)))


upairs :: Derivation -> [Upair]
upairs (Axiom (c,Variable x,typ))           = [(typ, find x c)]
upairs (Abstraction (c,Lambda x n,typ) d)   = (typ, aux_abs (conclusion d) x) : (upairs d)
  where
    aux_abs :: Judgement -> Var -> Type -- used for finding alpha and beta in an abtraction
    aux_abs (c,m,beta) x = (find x c) :-> beta
upairs (Application (c,Apply n m,typ) d dd) = (aux_app (conclusion d) (conclusion dd) typ) : ((upairs d) ++ (upairs dd))
  where
    aux_app :: Judgement -> Judgement -> Type -> Upair -- used for pattern matching of an application
    aux_app (c,m,gamma) (cc,n,alpha) beta = (gamma, alpha :-> beta)


derive :: Term -> Derivation
derive t = subs_der (unify (upairs (derive1 t))) (derive1 t)
