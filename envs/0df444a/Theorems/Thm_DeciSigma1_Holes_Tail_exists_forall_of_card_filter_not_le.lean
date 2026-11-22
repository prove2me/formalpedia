-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_exists_forall_of_card_filter_not_le
-- name    : DeciSigma1.Holes.Tail.exists_forall_of_card_filter_not_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:55:30.491338+00:00
-- url     : https://prove2.me/theorems/ca4ba044-ab7f-4dd0-a3eb-b659dc64d40b
-- title:
--   Tail: exists forall of card filter not le
-- statement:
--   Finite avoidance: if for each `u ∈ U` at most `c` elements of `R` fail `p u`, and
--   `|U| · c < |R|`, some element of `R` satisfies `p u` for every `u ∈ U`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Levels.lean#L673-L682
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Levels.lean#L673-L682

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

theorem DeciSigma1.Holes.Tail.exists_forall_of_card_filter_not_le {ι κ : Type*} {R : Finset κ} {U : Finset ι}
    (p : ι → κ → Prop) [∀ u, DecidablePred (p u)] {c : ℕ}
    (hbad : ∀ u ∈ U, (R.filter fun r => ¬ p u r).card ≤ c) (hlt : U.card * c < R.card) :
    ∃ r ∈ R, ∀ u ∈ U, p u r := by sorry
