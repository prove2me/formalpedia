-- Prove2me | Theorems.Thm_Auto_aux_ErgodicBox_cancel_box_ratio
-- name    : Auto.aux_ErgodicBox.cancel_box_ratio
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T17:43:57.518977+00:00
-- url     : https://prove2.me/theorems/912882a4-5581-4906-9913-9e5e9022f69d
-- title:
--   aux Ergodic Box: cancel box ratio
-- statement:
--   Cancels the inner-box cardinality after enlarging a side length from
--   `M` to `2M`.  This is the sole cardinality loss in the finite-box
--   ergodic-to-discrete reduction.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2456-L2478
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2456-L2478

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

theorem Auto.aux_ErgodicBox.cancel_box_ratio {n M : ℕ} (hM : 0 < M)
    {E A P : ℝ≥0∞}
    (h : ((box n M).card : ℝ≥0∞) * E ≤
      A * ((box n (M + M)).card : ℝ≥0∞) * P) :
    E ≤ A * ((2 ^ n : ℕ) : ℝ≥0∞) * P := by sorry
