-- Prove2me | Theorems.Thm_Auto_aux_pair_sq_le
-- name    : Auto.aux_pair_sq_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:40:01.187685+00:00
-- url     : https://prove2.me/theorems/a7eeacd9-abff-4ee2-9c5e-6a7ccd6bc2ec
-- title:
--   Auto: aux pair sq le
-- statement:
--   The squared fundamental-theorem/Cauchy--Schwarz estimate for one pair of
--   points in the finite variation chain.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L722-L760
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L722-L760

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem Auto.aux_pair_sq_le {α β x y : ℝ} (hα : 0 < α) (hαβ : α < β)
    (hx : x ∈ Set.Icc α β) (hy : y ∈ Set.Icc α β) (hxy : x ≤ y)
    (a : ℝ → ℝ) (ha : ContDiffOn ℝ 1 a (Set.Icc α β)) :
    ‖a y - a x‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal ((β - α) / α) *
      ∫⁻ t in Set.Icc x y, ‖t * deriv a t‖ₑ ^ (2 : ℝ)
        ∂aux_logarithmicMeasure α β := by sorry
