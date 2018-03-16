--{-# OPTIONS --without-K #-}
-- NOTE: insert gives a termination check warning if without-K is enabled. A bug?

module ListSet where

open import Data.List                             using (List; []; _∷_)
open import Relation.Binary.Core                  using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary                      using (yes; no)

record ListSet (A : Set) : Set where
  constructor listSet
  field
    set : List A
    eq  : Decidable {A = A} _≡_
open ListSet    

insert : {A : Set} → A → ListSet A → ListSet A
insert a (listSet []      e) = listSet (a ∷ []) e
insert a (listSet (b ∷ l) e) with e a b
insert a (listSet l@(b ∷ _) e) | yes p = listSet l e
insert a (listSet   (b ∷ l) e) | no ¬p = listSet (b ∷ set (insert a (listSet l e))) e
