-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_card_le_card_sub_one_of_injOn
-- name    : DeciSigma1.Holes.Tail.card_le_card_sub_one_of_injOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:54:05.858965+00:00
-- url     : https://prove2.me/theorems/aa142f29-8c14-486a-b68a-c127d85cc7a5
-- title:
--   Tail: card le card sub one of inj On
-- statement:
--   Counting by states: if the elements of `A`, ordered by an injective key, carry pairwise
--   distinct states other than `d`, then `A` has at most `N - 1` elements.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Levels.lean#L756-L768
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Levels.lean#L756-L768

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedFactors
public import Mathlib.Order.Nat
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Levels
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Holes.Periodic DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}

theorem DeciSigma1.Holes.Tail.card_le_card_sub_one_of_injOn {κ S : Type*} [Fintype S] (A : Finset κ)
    (key : κ → ℕ) (hkey : Set.InjOn key A) (f : κ → S) (d : S)
    (hinj : ∀ x ∈ A, ∀ y ∈ A, key x < key y → f x ≠ f y) (hd : ∀ x ∈ A, f x ≠ d) :
    A.card ≤ Fintype.card S - 1 := by sorry
