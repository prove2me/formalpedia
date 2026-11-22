-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_le_card_mul_of_gaps
-- name    : DeciSigma1.Holes.Fresh.le_card_mul_of_gaps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:06:13.600164+00:00
-- url     : https://prove2.me/theorems/9760f402-6312-47c4-a853-1e10adf4658e
-- title:
--   Fresh: le card mul of gaps
-- statement:
--   Bounded gaps in a finite set containing zero bound its largest member.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L624-L663
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L624-L663

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Bound
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α}
variable {S : Type} [Fintype S] [DecidableEq S] {T : Table α S k}

theorem DeciSigma1.Holes.Fresh.le_card_mul_of_gaps (A : Finset ℕ) (E : ℕ) (h0 : 0 ∈ A) (hgap : ∀ a ∈ A, ∀ b ∈ A, a < b →
      (∀ c ∈ A, ¬ (a < c ∧ c < b)) → b - a ≤ E) :
    ∀ x ∈ A, x ≤ A.card * E := by sorry
