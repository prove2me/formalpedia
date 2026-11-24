-- Prove2me | Theorems.Thm_BalanceSpecification_sGap_wordCount_le_renewal_sum
-- name    : BalanceSpecification.sGap_wordCount_le_renewal_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:06:18.819798+00:00
-- url     : https://prove2.me/theorems/83b0e96d-a904-401e-b1f8-6f7d8e260ad4
-- title:
--   Balance Specification: s Gap word Count le renewal sum
-- statement:
--   Actual S-gap language counts are bounded by a polynomial number of renewal counts.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapRenewal.lean#L283-L333
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapRenewal.lean#L283-L333

module
public import Definitions.Def_BalanceSpecificaton_SGap
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGapRenewal
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification

theorem BalanceSpecification.sGap_wordCount_le_renewal_sum [TopologicalSpace Bool] [DiscreteTopology Bool]
    {S : Set ℕ} (hS : S.Nonempty) (n : ℕ) :
    wordCount (language (sGapShift S)) n ≤
      1 + ∑ a ∈ Finset.range (n + 1), ∑ m ∈ Finset.range (n + 1),
        renewalCount S (n - a - m - 1) := by sorry
