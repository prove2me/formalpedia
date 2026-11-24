-- Prove2me | Theorems.Thm_BalanceSpecification_hasBoundedSuccessiveGaps_iff_uniform_right_completion
-- name    : BalanceSpecification.hasBoundedSuccessiveGaps_iff_uniform_right_completion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:46:52.20935+00:00
-- url     : https://prove2.me/theorems/b9b3720d-3cd7-4472-be3b-14e910eef9af
-- title:
--   Balance Specification: has Bounded Successive Gaps iff uniform right completion
-- statement:
--   A nonempty set has bounded successive gaps exactly when every initial
--   length that can be completed can be completed within a uniform extra length.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapBounds.lean#L36-L67
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapBounds.lean#L36-L67

module
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGapBounds
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification

theorem BalanceSpecification.hasBoundedSuccessiveGaps_iff_uniform_right_completion {S : Set ℕ}
    (hS : S.Nonempty) : HasBoundedSuccessiveGaps S ↔
      ∃ N : ℕ, ∀ t : ℕ, (∃ s ∈ S, t ≤ s) →
        ∃ s ∈ S, t ≤ s ∧ s ≤ t + N := by sorry
