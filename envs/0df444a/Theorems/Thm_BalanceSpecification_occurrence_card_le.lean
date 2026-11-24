-- Prove2me | Theorems.Thm_BalanceSpecification_occurrence_card_le
-- name    : BalanceSpecification.occurrence_card_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:56:56.744869+00:00
-- url     : https://prove2.me/theorems/b871a52f-fdfe-4dec-a3ee-57d26af70a3c
-- title:
--   Balance Specification: occurrence card le
-- statement:
--   The left/right context pair determines a word, so unconstrained side
--   counts give an upper bound.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/TwoSidedCounts.lean#L99-L109
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/TwoSidedCounts.lean#L99-L109

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

theorem BalanceSpecification.occurrence_card_le (u : Word A) (a b : ℕ) :
    (occurrenceFinset L u a b).card ≤ wordCount L a * wordCount L b := by sorry
