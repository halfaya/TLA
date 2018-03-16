{-# OPTIONS --without-K #-}

module Jugs where

open import Function                              using (_∘_)
open import Data.Empty                            using (⊥-elim)
open import Data.List                             using (List; []; _∷_; foldl; map)
open import Data.Nat                              using (ℕ; zero; suc; _+_; _≟_; _≤_; _≤?_; _∸_; z≤n; s≤s)
open import Data.Nat.Properties                   using (+-identityʳ; +-comm; +-assoc; +-suc)
open import Data.Product                          using (_×_; _,_; proj₁; proj₂)
open import Data.Product.Properties               using (,-injectiveˡ)
open import Relation.Binary.Core                  using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary                      using (yes; no; ¬_)

--------------
-- insert into a list if not already in the list

insertNoDup : {A : Set} → Decidable {A = A} _≡_ → A → List A → List A
insertNoDup e a [] = a ∷ []
insertNoDup e a (b ∷ l) with e a b
insertNoDup e a l@(b ∷ _) | yes p = l
insertNoDup e a (b ∷ l)   | no ¬p = b ∷ (insertNoDup e a l)

--------------

record Jug : Set where
  constructor jug
  field
    filled    : ℕ
    remaining : ℕ

  capacity : ℕ
  capacity = filled + remaining
open Jug

--------------
-- decidable equality for jugs and pairs of jugs

filled= : {j₁ j₂ : Jug} → j₁ ≡ j₂ → filled j₁ ≡ filled j₂
filled= {jug f _} {jug .f _} refl = refl

remaining= : {j₁ j₂ : Jug} → j₁ ≡ j₂ → remaining j₁ ≡ remaining j₂
remaining= {jug _ r} {jug _ .r} refl = refl

_J≟_ : Decidable {A = Jug} _≡_
jug filled₁ remaining₁ J≟ jug filled₂ remaining₂ with filled₁ ≟ filled₂ | remaining₁ ≟ remaining₂
... | yes p | yes q = yes (cong₂ jug p q)
... | yes p | no ¬q = no  (¬q ∘ remaining=)
... | no ¬p | _     = no  (¬p ∘ filled=)

-- ,-injectiveʳ in Data.Product.Properties requires the first components be the same but applies to general Σ
,-injectiveʳ× : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {ab cd : A × B} → ab ≡ cd → proj₂ ab ≡ proj₂ cd
,-injectiveʳ× refl = refl

_J₂≟_ : Decidable {A = Jug × Jug} _≡_
(a , b) J₂≟ (c , d) with a J≟ c | b J≟ d
... | yes p | yes q = yes (cong₂ _,_ p q)
... | yes p | no ¬q = no  (¬q ∘ ,-injectiveʳ×)
... | no ¬p | _     = no  (¬p ∘ ,-injectiveˡ)

JugPairSet : Set
JugPairSet = List (Jug × Jug)

--------------
-- steps

Step : Set
Step = Jug × Jug → Jug × Jug

fill₁ : Step
fill₁ (j₁ , j₂) = jug (capacity j₁) 0 , j₂

fill₂ : Step
fill₂ (j₁ , j₂) = j₁ , jug (capacity j₂) 0

empty₁ : Step
empty₁ (j₁ , j₂) = jug 0 (capacity j₁) , j₂

empty₂ : Step
empty₂ (j₁ , j₂) = j₁ , jug 0 (capacity j₂)

pour₁ : Step
pour₁ (from , to) with filled from ≤? remaining to
pour₁ (from , to) | yes p = jug 0 (remaining from + filled from) , jug (filled from + filled to) (remaining to ∸ filled from)
pour₁ (from , to) | no ¬p = jug (filled from ∸ remaining to) (remaining from + remaining to) , jug (capacity to) 0

pour₂ : Step
pour₂ (to , from) with filled from ≤? remaining to
pour₂ (to , from) | yes p = jug (filled from + filled to) (remaining to ∸ filled from) , jug 0 (remaining from + filled from)
pour₂ (to , from) | no ¬p = jug (capacity to) 0 , jug (filled from ∸ remaining to) (remaining from + remaining to)

------------
-- arithmetic lemmas

m+n-m=n : (m n : ℕ) → m ≤ n → m + (n ∸ m) ≡ n
m+n-m=n zero    _       _       = refl
m+n-m=n (suc m) zero    ()
m+n-m=n (suc m) (suc n) (s≤s p) = cong suc (m+n-m=n m n p)

m-k+n+k=m+n : (m k n : ℕ) → ¬ (m ≤ k) → m ∸ k + (n + k) ≡ m + n
m-k+n+k=m+n m       zero    n _ rewrite (+-identityʳ n) = refl
m-k+n+k=m+n zero    (suc k) n ¬p = ⊥-elim (¬p z≤n)
m-k+n+k=m+n (suc m) (suc k) n ¬p =
  let a : suc (m ∸ k + (n + k)) ≡ suc (m + n)           ; a = cong suc (m-k+n+k=m+n m k n (¬p ∘ s≤s))
      b : m ∸ k + suc (n + k)   ≡ suc (m ∸ k + (n + k)) ; b = +-suc (m ∸ k) (n + k)
      c : m ∸ k + (n + suc k)   ≡ m ∸ k + suc (n + k)   ; c = cong (m ∸ k +_) (+-suc n k)
  in trans c (trans b a)

------------
-- proofs that steps preserve capacity

PreservesCapacity : Step → Set
PreservesCapacity step = (jugpair : Jug × Jug) →
                         (capacity (proj₁ jugpair) ≡ capacity (proj₁ (step jugpair)) × capacity (proj₂ jugpair) ≡ capacity (proj₂ (step jugpair)))

data StepsPreserveCapacity : List Step → Set where
  []  : StepsPreserveCapacity []
  _∷_ : {s : Step} {ss : List Step} →
        (pc : PreservesCapacity s) → StepsPreserveCapacity ss → StepsPreserveCapacity (s ∷ ss)

fill₁PreservesCapacity : PreservesCapacity fill₁
fill₁PreservesCapacity (j₁ , j₂) rewrite (+-identityʳ (filled j₁ + remaining j₁)) = refl , refl

fill₂PreservesCapacity : PreservesCapacity fill₂
fill₂PreservesCapacity (j₁ , j₂) rewrite (+-identityʳ (filled j₂ + remaining j₂)) = refl , refl

empty₁PreservesCapacity : PreservesCapacity empty₁
empty₁PreservesCapacity (j₁ , j₂) = refl , refl

empty₂PreservesCapacity : PreservesCapacity empty₂
empty₂PreservesCapacity (j₁ , j₂) = refl , refl

pour₁PreservesCapacity : PreservesCapacity pour₁
pour₁PreservesCapacity (from , to) with filled from ≤? remaining to
... | yes p rewrite (+-comm (filled from) (remaining from)) |
                    (+-assoc (filled from) (filled to) (remaining to ∸ filled from)) |
                    (+-comm (filled to) (remaining to ∸ filled from)) |
                    (sym (+-assoc (filled from) (remaining to ∸ filled from) (filled to))) |
                    m+n-m=n (filled from) (remaining to) p |
                    (+-comm (filled to) (remaining to)) = refl , refl
... | no ¬p rewrite (+-identityʳ (filled to + remaining to)) |
                    (m-k+n+k=m+n (filled from) (remaining to) (remaining from) ¬p) = refl , refl

pour₂PreservesCapacity : PreservesCapacity pour₂
pour₂PreservesCapacity (to , from)  with filled from ≤? remaining to
... | yes p rewrite (+-comm (filled from) (remaining from)) |
                    (+-comm (filled from) (filled to)) |
                    (+-assoc (filled to) (filled from) (remaining to ∸ filled from) ) |
                    m+n-m=n (filled from) (remaining to) p
                    = refl , refl
... | no ¬p rewrite (+-identityʳ (filled to + remaining to)) |
                    (m-k+n+k=m+n (filled from) (remaining to) (remaining from) ¬p) = refl , refl

------------
-- specific steps

steps : List Step
steps = fill₁ ∷ fill₂ ∷ empty₁ ∷ empty₂ ∷ pour₁ ∷ pour₂ ∷ []

stepsPreserveCapacity : StepsPreserveCapacity steps
stepsPreserveCapacity = fill₁PreservesCapacity  ∷ fill₂PreservesCapacity  ∷
                        empty₁PreservesCapacity ∷ empty₂PreservesCapacity ∷
                        pour₁PreservesCapacity  ∷ pour₂PreservesCapacity  ∷ []

------------
-- applying steps to sets of jug pairs

-- returns the set that results after applying every step in steps to every jug pair in jugpairs
apply : List Step → JugPairSet → JugPairSet
apply steps jugpairs =
  foldl (λ acc jugpair → foldl (λ acc' jugpair' → insertNoDup _J₂≟_ jugpair' acc')
                               acc (map (λ step → step jugpair) steps))
        [] jugpairs

-- repeatedly apply n times function f to a base value
repeat : ∀ {ℓ} {A : Set ℓ} → ℕ → (A → A) → A → A
repeat zero    f a = a
repeat (suc n) f a = repeat n f (f a)

------------
-- Example: Can you measure 4 units of water using jugs with capacity 3 and 5?
-- This only shows that it's possible; it doesn't show a sequence of steps.

jug₁ : Jug
jug₁ = jug 0 5

jug₂ : Jug
jug₂ = jug 0 3

-- The smallest number of steps needed is 6.
solution : JugPairSet
solution = repeat 6 (apply steps) ((jug₁ , jug₂) ∷ [])
{- solution =
(jug 5 0 , jug 0 3) ∷
(jug 5 0 , jug 3 0) ∷
(jug 0 5 , jug 0 3) ∷
(jug 2 3 , jug 3 0) ∷
(jug 0 5 , jug 3 0) ∷
(jug 2 3 , jug 0 3) ∷
(jug 3 2 , jug 0 3) ∷
(jug 0 5 , jug 2 1) ∷
(jug 3 2 , jug 3 0) ∷
(jug 5 0 , jug 2 1) ∷
(jug 5 0 , jug 1 2) ∷
(jug 4 1 , jug 3 0) ∷
(jug 0 5 , jug 1 2) ∷
(jug 1 4 , jug 0 3) ∷ []
-}
