-- Prove2me | Theorems.Thm_Auto_aux_ErgodicBox_prod_mul_rpow_eq_mul_prod_rpow
-- name    : Auto.aux_ErgodicBox.prod_mul_rpow_eq_mul_prod_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:44:17.874682+00:00
-- url     : https://prove2.me/theorems/ebec964f-9009-5009-bdcd-79cd5b5e8ff7
-- title:
--   aux Ergodic Box: prod mul rpow eq mul prod rpow
-- statement:
--   The aux Ergodic Box construction uses the prod mul rpow eq mul prod rpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2576-L2588
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2576-L2588

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

theorem Auto.aux_ErgodicBox.prod_mul_rpow_eq_mul_prod_rpow
    {ι : Type*} (s : Finset ι) (B : ℝ≥0∞) (I : ι → ℝ≥0∞)
    (q : ι → ℝ) (hq : ∀ i ∈ s, 0 ≤ q i)
    (hqsum : ∑ i ∈ s, q i = 1) :
    ∏ i ∈ s, (B * I i) ^ q i = B * ∏ i ∈ s, I i ^ q i := by sorry
