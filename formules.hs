module Formules where

import Data.Set as Set (Set,
                         empty,
                         singleton,
                         union,
                         toList,
                         filter,
                         member,
                         notMember,
                         size,
                         map,
                         fold,
                         findMin, fromDistinctDescList, fromList, null, insert)
import Data.Map.Strict as Map (Map,
                               fromList,
                                (!))
import qualified Data.Bifunctor

data Formule = Vrai |
               Faux |
               Var String |
               Non Formule |
               Et Formule Formule |
               Ou Formule Formule

-- >>> (((Var "a" `Et` Var "b") `Ou` Faux) `Et` (Non (Var "c") `Et` Vrai))
-- (((a ∧ b) v ⊥) ∧ (¬c ∧ T))
formuleToString :: Formule -> String
formuleToString  Vrai =  "T"
formuleToString  Faux =  "⊥"
formuleToString  (Var v) =  v
formuleToString  (Non f) =  '¬' : formuleToString f
formuleToString  (Et f1 f2) = "(" ++ formuleToString f1 ++ " ∧ " ++ formuleToString f2 ++ ")"
formuleToString  (Ou f1 f2) = "(" ++ formuleToString f1 ++ " v " ++ formuleToString f2 ++ ")"

instance Show Formule where
  show  = formuleToString

-- >>> hauteur (((Var "a" `Et` Var "b") `Ou` Faux) `Et` (Non (Var "c") `Et` Vrai))
-- 3
-- >>> hauteur ((Var "b" `Et` Var "c") `Et` Var "a")
-- 2
hauteur :: Formule -> Int
hauteur Vrai = 0
hauteur Faux = 0
hauteur (Var v) = 0
hauteur (Non f) = hauteur f + 1
hauteur (Et f1 f2) = max (hauteur f1) (hauteur f2) + 1
hauteur (Ou f1 f2) = max (hauteur f1) (hauteur f2) + 1

-- >>> variables (((Var "a" `Et` Var "b") `Ou` Faux) `Et` (Non (Var "c") `Et` Vrai))
-- fromList ["a","b","c"]
-- >>> variables (((Var "c" `Et` Var "b") `Et` (Var "a")))
-- fromList ["a","b","c"]
variables :: Formule -> Set String
variables Faux = Set.empty
variables Vrai = Set.empty
variables (Var v) = Set.singleton v
variables (Non f) = variables f
variables (Et f1 f2) = variables f1 `Set.union` variables f2
variables (Ou f1 f2) = variables f1 `Set.union` variables f2

type Valuation = Map String Bool

sigma :: Valuation
sigma = Map.fromList [("a", True), ("b", True), ("c", False)]

-- >>> evaluate sigma (((Var "a" `Et` Var "b") `Ou` Faux) `Et` (Non (Var "c") `Et` Vrai))
-- True
-- >>> evaluate sigma (((Var "c" `Et` Var "b") `Et` (Var "a")))
-- False
evaluate :: Valuation -> Formule -> Bool
evaluate _ Vrai = True
evaluate _ Faux = False
evaluate v (Var var) = v ! var
evaluate v (Non f) = not (evaluate v f)
evaluate v (Et f1 f2) = evaluate v f1 && evaluate v f2
evaluate v (Ou f1 f2) = evaluate v f1 || evaluate v f2

-- >>> pushNegation (Non (Var "a" `Ou` (Non (Var "b") `Et` Var "c" )))
-- (¬a ∧ (b v ¬c))
pushNegation :: Formule -> Formule
pushNegation f =
    case f of
        -- double negation
        Non (Non f)    -> pushNegation f
        -- constant
        Non Vrai       -> Faux
        -- constant
        Non Faux       -> Vrai
        -- lois de Morgan
        Non (Et f1 f2) -> pushNegation (Non f1) `Ou` pushNegation (Non f2)
        Non (Ou f1 f2) -> pushNegation (Non f1) `Et` pushNegation (Non f2)
        -- recursivité sur les sous formules
        Et f1 f2       -> Et (pushNegation f1) (pushNegation f2)
        Ou f1 f2       -> Ou (pushNegation f1) (pushNegation f2)
        -- le reste
        f1             -> f1


-- >>> distribute ((Var "x" `Ou` Var "y") `Et` (Non (Var "z") `Ou` (Var "x"))) ((Var "t") `Et` (Var "s" `Ou` Non (Var "y")))
-- (((x v y) v t) ∧ (((x v y) v (s v ¬y)) ∧ (((¬z v x) v t) ∧ ((¬z v x) v (s v ¬y)))))
-- >>> distribute ((Var "A" `Ou` Var "B")) ((Var "C" `Ou` Var "D"))
-- ((A v B) v (C v D))
distribute :: Formule -> Formule -> Formule
distribute (Et f1 f2) (Et f3 f4)                                     = Et (Ou f1 f3) (Et (Ou f1 f4) (Et (Ou f2 f3) (Ou f2 f4)))
distribute f1 (Et f2 f3)                                             = (f1 `Ou` f2) `Et` (f1 `Ou` f3)
distribute (Et f1 f2) f3                                             = (f1 `Ou` f3) `Et` (f2 `Ou` f3)
distribute disj1@(Ou f1 f2) disj2@(Ou f3 f4)                         = disj1' `Ou` disj2'
                                                                      where disj1' = distribute f1 f2
                                                                            disj2' = distribute f3 f4
distribute (Var v1) (Var v2)                                         = Var v1 `Ou` Var v2
distribute (Var v)  disj@(Ou f1 f2)                                  = Var v `Ou` disj
distribute disj@(Ou f1 f2) (Var v)                                   = disj `Ou` Var v
distribute f neg@(Non (Var v2))                                      = f `Ou` neg
distribute neg@(Non (Var v1)) f                                      = neg `Ou` f

-- >>> fnc (((Var "A" `Ou` Var "B") `Ou` Var "E") `Ou` (Var "C" `Ou` Var "D"))
-- >>> ((Var "A" `Et` Var "B") `Ou` (Var "C" `Et` Var "D"))
-- >>> fnc (((Var "A" `Et` Var "X")`Ou` Var "B") `Ou` (Var "C" `Ou` Var "D"))
-- >>> fnc ((Var "A" `Ou` Var "X") `Et` (Var "B" `Et` (Var "C" `Ou` Var "D")))
-- >>> fnc ((Var "A" `Et` Var "B") `Ou` (Var "C" `Et` Var "D"))
-- >>> fnc (Non(Var "C" `Ou` Var "B"))
-- (((A v B) v E) v (C v D))
-- ((A ∧ B) v (C ∧ D))
-- (((A v B) v (C v D)) ∧ ((X v B) v (C v D)))
-- ((A v X) ∧ (B ∧ (C v D)))
-- ((A v C) ∧ ((A v D) ∧ ((B v C) ∧ (B v D))))
-- (¬C ∧ ¬B)
fnc :: Formule -> Formule
fnc litteral@(Var v) = litteral
fnc (Non (Var v))    = Non $ Var v
fnc (Et f1 f2)       = fnc f1 `Et` fnc f2
fnc (Ou f1 f2)       = distribute (fnc (pushNegation f1)) (fnc (pushNegation f2))
fnc (Non f)          = pushNegation (Non $ fnc f)

type Clause =  Set Int
type SAT = Set Clause

-- >>> varsToInt (Set.fromList ["a", "b"])
-- (fromList [("a",1),("b",2)],fromList [(1,"a"),(2,"b")])
varsToInt :: Set String -> (Map String Int, Map Int String)
varsToInt s = (encode, decode)
              where
                encode = Map.fromList[(Set.toList s !! (i-1), i) | i <- [1 .. size s]]
                decode = Map.fromList[(i, Set.toList s !! (i-1)) | i <- [1 .. size s]]

-- >>> varRepresentation (((Var "a" `Et` Var "b") `Ou` Faux) `Et` (Non (Var "c") `Et` Vrai))
-- (fromList [("a",1),("b",2),("c",3)],fromList [(1,"a"),(2,"b"),(3,"c")])
varRepresentation :: Formule -> (Map String Int, Map Int String)
varRepresentation f = varsToInt (variables f)

fncToSAT :: Map String Int -> Formule -> SAT
fncToSAT m f =  case f of
                    Et x y -> fncToSAT m x `union` fncToSAT m y
                    Ou x y -> Set.fromList [Set.fromList (convOu x ++ convOu y)]
                    Var v  -> Set.fromList [Set.fromList[m ! v]]
                    Non (Var v) ->  Set.fromList [Set.fromList[-(m ! v)]]
                where
                    convOu (Ou x y) = convOu x ++ convOu y
                    convOu (Var v)  = [m ! v]
                    convOu (Non (Var v)) = [-(m ! v)]

-- >>> f = (Var "a") 
-- >>> f
-- >>> formuleToSAT f
-- a
-- fromList [fromList [1]]
-- >>> f = (Var "a" `Ou` Var "b") 
-- >>> f
-- >>> formuleToSAT f
-- (a v b)
-- fromList [fromList [1,2]]
-- >>> f = ((Var "a" `Ou` Var "b") `Et` (Non (Var "c") `Ou` (Var "a"))) 
-- >>> f
-- >>> formuleToSAT f
-- ((a v b) ∧ (¬c v a))
-- fromList [fromList [-3,1],fromList [1,2]]
-- >>> f = ((Var "a" `Ou` Var "b") `Et` ((Var "c") `Ou` (Var "a"))) 
-- >>> f
-- >>> formuleToSAT f
-- ((a v b) ∧ (c v a))
-- fromList [fromList [1,2],fromList [1,3]]
-- >>> f = (Non (Var "a") `Et` (Var "b" `Ou` Non (Var "c"))) 
-- >>> f
-- >>> formuleToSAT f 
-- (¬a ∧ (b v ¬c))
-- fromList [fromList [-3,2],fromList [-1]]
-- >>> f = (Var "a" `Ou` Var "b") `Et` Var "c" 
-- >>> f
-- >>> formuleToSAT f
-- ((a v b) ∧ c)
-- fromList [fromList [1,2],fromList [3]]
formuleToSAT :: Formule -> SAT
formuleToSAT f = fncToSAT (fst(varRepresentation f)) (fnc f)

-- >>> isTrivial (Set.fromList[1, 3])
-- False
-- >>> isTrivial (Set.fromList[1, 2, 3, -2])
-- True
isTrivial :: Clause -> Bool
isTrivial c = any (\x -> (-x) `member` c) c

-- >>> f = ((Non (Var "a") `Ou` Var "a") `Et` Var "b")
-- >>> f
-- >>> sat = formuleToSAT f 
-- >>> simplification sat
-- ((¬a v a) ∧ b)
-- fromList [fromList [2]]
simplification :: SAT -> SAT
simplification  = Set.filter (not . isTrivial)

-- >>> f = (Var "a" `Ou` (Non(Var "b"))) `Et` ((Var "b"))
-- >>> f
-- >>> sat = formuleToSAT f 
-- >>> sat
-- >>> propagate 2 sat
-- ((a v ¬b) ∧ b)
-- fromList [fromList [-2,1],fromList [2]]
-- fromList [fromList [1]]
propagate :: Int -> SAT -> SAT
propagate k s = Set.map ( Set.filter (/= -k)) (Set.filter(not . member k) s )

literals :: SAT -> Set Int
literals = fold union empty

-- >>> isUnitary (Set.fromList [1])
-- True
-- >>> isUnitary (Set.fromList [1, 2])
-- False
isUnitary :: Clause -> Bool
isUnitary c = Set.size c == 1

-- >>> f = ((Var "a" `Ou` (Non(Var "b"))) `Et` (Var "b")) `Et` (Var "c")
-- >>> f
-- >>> sat = formuleToSAT f 
-- >>> literalsInUnitaryClauses sat
-- (((a v ¬b) ∧ b) ∧ c)
-- fromList [2,3]
literalsInUnitaryClauses :: SAT -> Set Int
literalsInUnitaryClauses s = literals (Set.filter isUnitary s)

-- >>> f = ((Var "a" `Ou` (Non(Var "b"))) `Et` (Var "b")) `Et` (Var "b")
-- >>> f
-- >>> sat = formuleToSAT f 
-- >>> contradiction sat
-- (((a v ¬b) ∧ b) ∧ b)
-- False
contradiction :: SAT -> Bool
contradiction s = any (\x -> (-x) `member` literalsInUnitaryClauses s) (literalsInUnitaryClauses s)

-- >>> f = ((Var "a" `Ou` (Non(Var "b"))) `Et` (Non(Var "b"))) `Et` ((Non(Var "b")) `Ou` (Var "c") `Ou` (Non(Var "a")))
-- >>> f
-- >>> sat = formuleToSAT f 
-- >>> pureLiterals sat
-- (((a v ¬b) ∧ ¬b) ∧ ((¬b v c) v ¬a))
-- fromList [-2,3]
pureLiterals :: SAT -> Set Int
pureLiterals s =  Set.filter (\x -> notMember (-x) purs) purs
                  where
                     purs = literals s

-- sol = solution (ensemble des littéraux qui satisfont le prob)
-- sat = le prob sat
dpllAux :: Set Int -> SAT -> Maybe(Set Int)
dpllAux sol sat
    | Set.null sat     = Just sol
    | any Set.null sat = Nothing
    | otherwise =
        case Set.toList(literalsInUnitaryClauses sat)  of
          (x:xs') -> dpllAux (Set.insert x sol) (propagate x sat)
          []      ->
            let pivot        = Set.findMin (literals sat)
                positiveCase = dpllAux (Set.insert pivot sol) (propagate pivot sat)
                negativeCase = dpllAux (Set.insert (-pivot) sol ) (propagate (-pivot) sat)
            in case positiveCase of
              Nothing -> negativeCase
              Just xs -> Just xs


-- >>> f = ((Non(Var "p") `Ou` Var "t") `Et` (Var "p" `Ou` Non(Var "r")) `Et` (Var "q" `Ou` Var "r") `Et` (Non(Var "q") `Ou` Var "s"))
-- >>> f
-- >>> sat = formuleToSAT f
-- >>> sat
-- >>> dpll sat
-- ((((¬p v t) ∧ (p v ¬r)) ∧ (q v r)) ∧ (¬q v s))
-- fromList [fromList [-3,1],fromList [-2,4],fromList [-1,5],fromList [2,3]]
-- Just (fromList [-3,-1,2,4])
dpll :: SAT -> Maybe (Set Int)
dpll s = dpllAux Set.empty (simplification s)

-- >>> f = (Var "p" `Et` ((Var "q" `Ou` Var "s") `Et` (Non(Var "q") `Ou` Non(Var "p")) `Et` Var "r"))
-- >>> f
-- (p ∧ (((q v s) ∧ (¬q v ¬p)) ∧ r))
-- >>> solve f
-- Just (fromList [("p",True),("q",False),("r",True),("s",True)])
solve :: Formule -> Maybe Valuation
solve f = let res = dpll (formuleToSAT f)
              rep = snd(varRepresentation f)
          in case res of
            Nothing -> Nothing
            Just s  -> Just (Map.fromList[Data.Bifunctor.first (rep !) (index (i - 1) (Set.toList s)) | i <- [1 .. Set.size s]])
              where
                index :: Int -> [Int] -> (Int, Bool)
                index i s = if s !! i < 0
                              then (-(s !! i), False)
                            else
                              (s !! i, True)
