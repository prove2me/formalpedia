-- Prove2me | Theorems.Thm_BalanceSpecification_occurrence_card_eq_sum
-- name    : BalanceSpecification.occurrence_card_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:46:17.610846+00:00
-- url     : https://prove2.me/theorems/42ae9f5a-4823-4b2b-8253-90001b87cb9c
-- title:
--   Balance Specification: occurrence card eq sum
-- statement:
--   The Balance Specification construction uses the occurrence card eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/TwoSidedCounts.lean#L36-L61
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/TwoSidedCounts.lean#L36-L61

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

theorem BalanceSpecification.occurrence_card_eq_sum (u : Word A) (a b : ℕ) :
    (occurrenceFinset L u a b).card =
      ∑ p ∈ predecessorFinset L u a, (followerFinset L (p ++ u) b).card := by sorry
