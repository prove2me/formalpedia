-- Prove2me | Theorems.Thm_Auto_aux_ErgodicBox_prod_rpow_eq_rpow_sum_of_nonneg
-- name    : Auto.aux_ErgodicBox.prod_rpow_eq_rpow_sum_of_nonneg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T17:44:17.446864+00:00
-- url     : https://prove2.me/theorems/1235a602-e8c5-426b-9f2c-e63aa877ee71
-- title:
--   aux Ergodic Box: prod rpow eq rpow sum of nonneg
-- statement:
--   The aux Ergodic Box construction uses the prod rpow eq rpow sum of nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2562-L2574
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2562-L2574

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
open Auto.aux_ErgodicBox
open MeasureTheory Set
open scoped ENNReal BigOperators

theorem Auto.aux_ErgodicBox.prod_rpow_eq_rpow_sum_of_nonneg
    {ι : Type*} (s : Finset ι) (B : ℝ≥0∞) (q : ι → ℝ)
    (hq : ∀ i ∈ s, 0 ≤ q i) :
    ∏ i ∈ s, B ^ q i = B ^ (∑ i ∈ s, q i) := by sorry
