-- Prove2me | Theorems.Thm_Auto_aux_lrpow_three_le
-- name    : Auto.aux_lrpow_three_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:38:24.949788+00:00
-- url     : https://prove2.me/theorems/f2361288-bca5-40c8-9797-1d7e56745397
-- title:
--   Auto: aux lrpow three le
-- statement:
--   The finite-dimensional three-term Minkowski estimate used in
--   `shortlongJumps`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L56-L74
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L56-L74

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem Auto.aux_lrpow_three_le {M : ℕ} (r : ℝ) (hr : 1 ≤ r)
    (d u v w : Fin M → ℝ≥0∞)
    (h : ∀ j, d j ≤ u j + v j + w j) :
    (∑ j, d j ^ r) ^ r⁻¹ ≤
      (∑ j, u j ^ r) ^ r⁻¹ + (∑ j, v j ^ r) ^ r⁻¹ +
        (∑ j, w j ^ r) ^ r⁻¹ := by sorry
