module BST.BSTree where

open import BST.Tree

open import Data.Bool
open import Data.Nat hiding (compare)
open import Data.Nat.Compare
open import Data.Nat.Theorems
open import Data.Sum
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

wrapT₁ : {n k : ℕ} → Tree ℕ n ⊎ Tree ℕ (1 + n) → ℕ → Tree ℕ k → Tree ℕ (1 + n + k) ⊎ Tree ℕ (1 + (1 + n) + k)
wrapT₁ (inj₁ x) v t = inj₁ < x , v , t >
wrapT₁ (inj₂ y) v t = inj₂ < y , v , t >

wrapT₂ : {n k : ℕ} → Tree ℕ n ⊎ Tree ℕ (1 + n) → ℕ → Tree ℕ k → Tree ℕ (1 + k + n) ⊎ Tree ℕ (1 + k + (1 + n))
wrapT₂ (inj₁ x) v t = inj₁ < t , v , x >
wrapT₂ (inj₂ y) v t = inj₂ < t , v , y >

insert : {n : ℕ} → (v : ℕ) → (t : Tree ℕ n) → Tree ℕ n ⊎ Tree ℕ (1 + n)
insert v □ = inj₂ < □ , v , □ >
insert v < l , a , r > with compare v a
insert v < l , a , r > | LT = wrapT₁ (insert v l) a r
insert v < l , a , r > | EQ = inj₁ < l , a , r >
insert v < l , a , r > | GT = subst (λ x → Tree ℕ (suc (size l + size r)) ⊎ Tree ℕ (suc x)) 
                              (sym (lem-plus-s (size l) (size r))) 
                              (wrapT₂ (insert v r) a l)

-- tree membership

data In : {n : ℕ} → ℕ → (Tree ℕ n) → Set where
  in-elem   : {n m : ℕ} (a : ℕ) (l : Tree ℕ n) → (r : Tree ℕ m) → In a < l , a , r >
  in-below₁ : {n m : ℕ} (a : ℕ) (t : Tree ℕ n) (v : ℕ) (r : Tree ℕ m) (p : compare a v ≡ LT) (i : In a t) → In a < t , v , r >
  in-below₂ : {n m : ℕ} (a : ℕ) (t : Tree ℕ n) (v : ℕ) (l : Tree ℕ m) (p : compare a v ≡ GT) (i : In a t) → In a < l , v , t >
{-
lem-insert-existing : {n : ℕ} → (a : ℕ) → (t : Tree ℕ n) → In a t → insert a t ≡ inj₁ t 
lem-insert-existing a .(< l , a , r >) (in-elem .a l r) with (lem-compare-refl a) 
... | p rewrite p = refl
lem-insert-existing a .(< t , v , r >) (in-below₁ .a t v r p i) rewrite p with lem-insert-existing a t i
... | lem rewrite lem = refl
lem-insert-existing a .(< l , v , t >) (in-below₂ .a t v l p i) rewrite p with lem-insert-existing a t i
... | lem rewrite lem = {!!} -- I don't know how to get throught that subst
 -- a similiar theorem can be proved if insert is defined slightly different
-}

{- Another version of insert with wrapT₂ fused -}

insert2 : {n : ℕ} → (v : ℕ) → (t : Tree ℕ n) → Tree ℕ n ⊎ Tree ℕ (1 + n)
insert2 v □ = inj₂ < □ , v , □ >
insert2 v < l , a , r > with compare v a
insert2 v < l , a , r > | LT = wrapT₁ (insert2 v l) a r
insert2 v < l , a , r > | EQ = inj₁ < l , a , r >
insert2 v < l , a , r > | GT with insert2 v r
... | inj₁ t = inj₁ (< l , a , t >)
... | inj₂ t = inj₂ (subst (λ x → Tree ℕ (suc x)) (sym (lem-plus-s (size l) (size r))) < l , a , t >)

lem-insert2-existing : {n : ℕ} → (a : ℕ) → (t : Tree ℕ n) → In a t → insert2 a t ≡ inj₁ t 
lem-insert2-existing a .(< l , a , r >) (in-elem .a l r)         rewrite lem-compare-refl a = refl
lem-insert2-existing a .(< t , v , r >) (in-below₁ .a t v r p i) rewrite p with lem-insert2-existing a t i 
... | lem rewrite lem = refl
lem-insert2-existing a .(< l , v , t >) (in-below₂ .a t v l p i) rewrite p with lem-insert2-existing a t i
... | lem rewrite lem = refl


data Sorted : {n : ℕ} → Tree ℕ n → Set where
  sorted-□  : Sorted □
  sorted-<> : {n m : ℕ}(a : ℕ)(l : Tree ℕ n)(r : Tree ℕ m)
              (sl : Sorted l)
              (sr : Sorted r) 
              (pl : ∀ n → In n l → compare n a ≡ LT) 
              (pr : ∀ n → In n r → compare n a ≡ GT) 
              → Sorted < l , a , r >


tree-rightmost : { n : ℕ } → Tree ℕ (suc n) → ℕ
tree-rightmost < l , a , □ > = a
tree-rightmost < l , a , < l' , a' , r > > = tree-rightmost < l' , a' , r >

lem-tree-max-sorted-in : ∀ {n} (t : Tree ℕ (suc n)) → Sorted t → In (tree-rightmost t) t
lem-tree-max-sorted-in .(< l , a , □ >) (sorted-<> a l □ sl sr pl pr) = in-elem a l □
lem-tree-max-sorted-in .(< l , a , < l' , a' , r > >) (sorted-<> a l < l' , a' , r > sl sr pl pr) = 
  in-below₂ (tree-rightmost < l' , a' , r >) < l' , a' , r > a l
  (pr (tree-rightmost < l' , a' , r >) 
  (lem-tree-max-sorted-in < l' , a' , r > sr))
  (lem-tree-max-sorted-in < l' , a' , r > sr)

lem-tree-max-sorted-is-max : ∀ {n} (t : Tree ℕ (suc n)) → Sorted t → (∀ a → In a t → a ≡ (tree-rightmost t) ⊎ compare a (tree-rightmost t) ≡ LT)
lem-tree-max-sorted-is-max .(< l , a , □ >) (sorted-<> .a .l .□ sl sr pl pr) a (in-elem .a l □) = inj₁ refl
lem-tree-max-sorted-is-max .(< l , a , < l' , a' , r > >) (sorted-<> .a .l .(< l' , a' , r >) sl sr pl pr) a (in-elem .a l < l' , a' , r >) = inj₂ (lem-compare-swap {n = a} (pr (tree-rightmost < l' , a' , r >) (lem-tree-max-sorted-in < l' , a' , r > sr)))
lem-tree-max-sorted-is-max .(< t , v , □ >) s a (in-below₁ .a t v □ p i) = inj₂ p
lem-tree-max-sorted-is-max .(< t , v , < l , a' , r > >) (sorted-<> .v .t .(< l , a' , r >) sl sr pl pr) a (in-below₁ .a t v < l , a' , r > p i) = inj₂ (lem-compare-trans-lt {m = a} p (lem-compare-swap {m = tree-rightmost < l , a' , r >} (pr (tree-rightmost < l , a' , r >) (lem-tree-max-sorted-in < l , a' , r > sr))))
lem-tree-max-sorted-is-max .(< l , v , □ >) s a (in-below₂ .a □ v l p ())
lem-tree-max-sorted-is-max .(< l' , v , < l , a' , r > >) (sorted-<> .v .l' .(< l , a' , r >) sl sr pl pr) a (in-below₂ .a < l , a' , r > v l' p i) = lem-tree-max-sorted-is-max < l , a' , r > sr a i


lem-member-left : {n m : ℕ} (l : Tree ℕ n) (r : Tree ℕ m) (a v : ℕ)
      (s : Sorted < l , v , r >) (c : compare a v ≡ LT) (i : ¬ In a l) → ¬ In a < l , v , r >
lem-member-left l r .v v s c i (in-elem .v .l .r) rewrite lem-compare-refl v = EQ≠LT c
lem-member-left l r a v s c i (in-below₁ .a .l .v .r p i') = i i'
lem-member-left l r a v s c i (in-below₂ .a .r .v .l p i') rewrite c = LT≠GT p

lem-member-right : {n m : ℕ} (l : Tree ℕ n) (r : Tree ℕ m) (a v : ℕ)
      (s : Sorted < l , v , r >) (c : compare a v ≡ GT) (i : ¬ In a r) → ¬ In a < l , v , r >
lem-member-right l r .v v s c i (in-elem .v .l .r) rewrite lem-compare-refl v = EQ≠GT c 
lem-member-right l r a v s c i (in-below₁ .a .l .v .r p i') rewrite c = GT≠LT p
lem-member-right l r a v s c i (in-below₂ .a .r .v .l p i') = i i'


member-dec : {n : ℕ} (t : Tree ℕ n) (a : ℕ) → Sorted t → Dec (In a t)
member-dec □ s a = no (λ ())
member-dec < l , v , r > a s with inspect (compare a v)
member-dec < l , v , r > a (sorted-<> .v .l .r sl sr pl pr) | LT with-≡ eq with member-dec l a sl
member-dec < l , v , r > a (sorted-<> .v .l .r sl sr pl pr) | LT with-≡ eq | yes p = 
  yes (in-below₁ a l v r (pl a p) p)
member-dec < l , v , r > a (sorted-<> .v .l .r sl sr pl pr) | LT with-≡ eq | no ¬p = 
  no (lem-member-left l r a v (sorted-<> v l r sl sr pl pr) eq ¬p)
member-dec < l , v , r > a (sorted-<> .v .l .r sl sr pl pr) | GT with-≡ eq with member-dec r a sr 
member-dec < l , v , r > a (sorted-<> .v .l .r sl sr pl pr) | GT with-≡ eq | yes p = 
  yes (in-below₂ a r v l (pr a p) p)
member-dec < l , v , r > a (sorted-<> .v .l .r sl sr pl pr) | GT with-≡ eq | no ¬p = 
  no (lem-member-right l r a v (sorted-<> v l r sl sr pl pr) eq ¬p)
member-dec < l , v , r > a (sorted-<> .v .l .r sl sr pl pr) | EQ with-≡ eq = yes (subst (λ x → In x < l , v , r >) (sym (lem-compare-eq eq)) (in-elem v l r))
