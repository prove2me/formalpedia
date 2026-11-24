-- Prove2me | Theorems.Thm_BalanceSpecification_occurrence_card_lower
-- name    : BalanceSpecification.occurrence_card_lower
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:56:58.843067+00:00
-- url     : https://prove2.me/theorems/057d53f8-03eb-4f81-8cbc-e4f7158f48a6
-- title:
--   Balance Specification: occurrence card lower
-- statement:
--   Uniform right-extension bounds and a left-extension bound multiply to a
--   lower bound for the number of admissible contexts of a fixed middle word.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/TwoSidedCounts.lean#L113-L130
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/TwoSidedCounts.lean#L113-L130

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

theorem BalanceSpecification.occurrence_card_lower {u : Word A} {a b : ℕ} {cL cR : ℝ}
    (hcR : 0 ≤ cR)
    (hR : ∀ v ∈ L, cR * (wordCount L b : ℝ) ≤ (followerFinset L v b).card)
    (hP : cL * (wordCount L a : ℝ) ≤ (predecessorFinset L u a).card) :
    cL * cR * (wordCount L a : ℝ) * wordCount L b ≤
      (occurrenceFinset L u a b).card := by sorry
