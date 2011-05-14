module BST.Tree where

open import Data.Bool
open import Data.Nat
open import Data.Nat.Theorems
open import Data.Vec renaming (_∷_ to _v∷_ ; _++_ to _v++_ ; reverse to vreverse)
-- open import Data.Vec.Theorems
open import Data.List
open import Data.List.Theorems
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning


{- The tree datatype -}

data Tree (A : Set) : ℕ → Set where
  □ : Tree A 0
  <_,_,_> : forall {n m} → (l : Tree A n) → (a : A) → (r : Tree A m) → Tree A (1 + n + m)


{- Two equivalent ways to count the number of elements in a tree -}

size : {A : Set}{n : ℕ} → Tree A n → ℕ
size {_} {n} _ = n

size-count : {A : Set}{n : ℕ} → Tree A n → ℕ
size-count □ = 0
size-count < l , a , r > = 1 + size-count l + size-count r

-- proof of equivalence

lem-size-equiv : ∀ {A n} (t : Tree A n) → size t ≡ size-count t
lem-size-equiv □            = refl
lem-size-equiv < l , a , r > = cong₂ (λ x y → suc (x + y)) (lem-size-equiv l) (lem-size-equiv r)


{- Calculating the fringe of the tree in two ways -}

vfringe-l : {A : Set}{n : ℕ} → Tree A n → Vec A n
vfringe-l □ = []
vfringe-l {A} < l , a , r > = subst (Vec A) (sym (lem-plus-s (size l) (size r))) 
                             (vfringe-l l v++ (a v∷ []) v++ vfringe-l r)

vfringe-r : {A : Set}{n : ℕ} → Tree A n → Vec A n
vfringe-r □ = []
vfringe-r {A} < l , a , r > = subst (Vec A) (trans (sym (lem-plus-s (size r) (size l))) (cong suc (lem-plus-comm (size r) (size l)))) 
                             (vfringe-r r v++ (a v∷ []) v++ vfringe-r l)

-- the relation between the two vfringe functions
{-
lem-vfringe-rel : ∀ {A n} → (t : Tree A n) → vfringe-l t ≡ vreverse (vfringe-r t)
lem-vfringe-rel □ = refl
lem-vfringe-rel < l , a , r > = {!!} 
-}
-- we need a lemma that states what happens will ++ and reverse


{- The same fringe calculation but using lists -}

fringe-l : {A : Set}{n : ℕ} → Tree A n → List A
fringe-l □ = []
fringe-l < l , a , r > = fringe-l l ++ (a ∷ []) ++ fringe-l r

fringe-r : {A : Set}{n : ℕ} → Tree A n → List A
fringe-r □ = []
fringe-r < l , a , r > = fringe-r r ++ (a ∷ []) ++ fringe-r l

-- Some properties of the fringe functions

lem-fringe-l-len : ∀ {A n} → (t : Tree A n) → length (fringe-l t) ≡ n
lem-fringe-l-len □ = refl
lem-fringe-l-len < l , a , r > = begin 
               length (fringe-l < l , a , r > )                 ≡⟨ refl ⟩ 
               length (fringe-l l ++ (a ∷ []) ++ fringe-l r)    ≡⟨ lem-length-app (fringe-l l) (a ∷ fringe-l r) ⟩ 
               length (fringe-l l) + length (a ∷ fringe-l r)    ≡⟨ sym (lem-plus-s (length (fringe-l l)) (length (fringe-l r))) ⟩
               suc (length (fringe-l l) + length (fringe-l r))  ≡⟨ cong₂ (λ x y → suc (x + y)) (lem-fringe-l-len l) (lem-fringe-l-len r) ⟩ 
               (suc (size l + size r)) ∎


lem-fringe-rel : ∀ {A n} → (t : Tree A n) → fringe-l t ≡ reverse (fringe-r t)
lem-fringe-rel □ = refl
lem-fringe-rel < l , a , r > = begin
  fringe-l < l , a , r >                                     ≡⟨ refl ⟩ 
  fringe-l l ++ (a ∷ []) ++ fringe-l r                       ≡⟨ cong₂ (λ x y → x ++ (a ∷ []) ++ y) (lem-fringe-rel l) (lem-fringe-rel r) ⟩
  reverse (fringe-r l) ++ ((a ∷ []) ++ reverse (fringe-r r)) ≡⟨ lem-app-assoc (reverse (fringe-r l)) (a ∷ []) (reverse (fringe-r r)) ⟩
 (reverse (fringe-r l) ++ (a ∷ [])) ++ reverse (fringe-r r)  ≡⟨ cong (λ x → x ++ reverse (fringe-r r)) (sym (lem-reverse-head a (fringe-r l))) ⟩ 
  reverse (a ∷ fringe-r l) ++ reverse (fringe-r r)           ≡⟨ sym (lem-reverse-app (fringe-r r) (a ∷ fringe-r l)) ⟩
  reverse (fringe-r r ++ (a ∷ []) ++ fringe-r l)             ≡⟨ refl ⟩
  reverse (fringe-r < l , a , r >) ∎
