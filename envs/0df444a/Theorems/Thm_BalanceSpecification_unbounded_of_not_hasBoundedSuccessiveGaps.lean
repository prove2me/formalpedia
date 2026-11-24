-- Prove2me | Theorems.Thm_BalanceSpecification_unbounded_of_not_hasBoundedSuccessiveGaps
-- name    : BalanceSpecification.unbounded_of_not_hasBoundedSuccessiveGaps
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:58:29.021337+00:00
-- url     : https://prove2.me/theorems/e180a6ea-f64f-4a48-935a-d07d0ddcc2b2
-- title:
--   Balance Specification: unbounded of not has Bounded Successive Gaps
-- statement:
--   Sets with unbounded successive gaps are unbounded above.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapBounds.lean#L89-L93
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapBounds.lean#L89-L93

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

theorem BalanceSpecification.unbounded_of_not_hasBoundedSuccessiveGaps {S : Set ℕ}
    (hS : ¬HasBoundedSuccessiveGaps S) : ∀ k : ℕ, ∃ b ∈ S, k < b := by sorry
