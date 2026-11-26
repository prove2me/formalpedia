-- Prove2me | Theorems.Thm_Auto_aux_diagonal_sum_le
-- name    : Auto.aux_diagonal_sum_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:39:24.89434+00:00
-- url     : https://prove2.me/theorems/362985bc-2fef-4fa2-aa40-62c25ba0ce14
-- title:
--   Auto: aux diagonal sum le
-- statement:
--   A diagonal finite sum is bounded by the sum of all its fibers.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L339-L348
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L339-L348

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem Auto.aux_diagonal_sum_le {J : ℕ} {κ : Finset ℤ} (c : Fin J → ℤ)
    (hc : ∀ j, c j ∈ κ) (F : ℤ → Fin J → ℝ≥0∞) :
    ∑ j, F (c j) j ≤ ∑ k ∈ κ, ∑ j, F k j := by sorry
