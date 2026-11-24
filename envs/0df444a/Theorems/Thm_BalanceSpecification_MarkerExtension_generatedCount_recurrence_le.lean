-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_generatedCount_recurrence_le
-- name    : BalanceSpecification.MarkerExtension.generatedCount_recurrence_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:03:59.338357+00:00
-- url     : https://prove2.me/theorems/7b9f7a1f-9de5-4f28-b3eb-a84a35cbbfac
-- title:
--   Marker Extension: generated Count recurrence le
-- statement:
--   Counting all possible first-generator lengths gives the renewal upper
--   recurrence. No unique parsing premise is needed for this direction.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkedRenewal.lean#L59-L86
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkedRenewal.lean#L59-L86

module
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Definitions.Def_BalanceSpecificaton_RenewalBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkedRenewal
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.MarkerExtension
variable {A : Type*} [Fintype A]

theorem BalanceSpecification.MarkerExtension.generatedCount_recurrence_le (P : Set (Word A)) (n : ℕ) :
    generatedCount P (n + 1) ≤
      ∑ l ∈ Finset.range (n + 1), generatorCount P (l + 1) * generatedCount P (n - l) := by sorry
