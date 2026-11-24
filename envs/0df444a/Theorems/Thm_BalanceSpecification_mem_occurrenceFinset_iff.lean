-- Prove2me | Theorems.Thm_BalanceSpecification_mem_occurrenceFinset_iff
-- name    : BalanceSpecification.mem_occurrenceFinset_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:56:56.592039+00:00
-- url     : https://prove2.me/theorems/1d43625d-30ee-4a73-9b0e-3781529e0a0e
-- title:
--   Balance Specification: mem occurrence Finset iff
-- statement:
--   The Balance Specification construction uses the mem occurrence Finset iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/TwoSidedCounts.lean#L63-L95
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/TwoSidedCounts.lean#L63-L95

module
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Data.Finset.Sigma
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_TwoSidedCounts
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*} [Fintype A] {L : Set (Word A)}

theorem BalanceSpecification.mem_occurrenceFinset_iff (hL : IsFactorial L) {u w : Word A} {a b : ℕ} :
    w ∈ occurrenceFinset L u a b ↔
      w ∈ L ∧ w.length = a + u.length + b ∧ (w.drop a).take u.length = u := by sorry
