-- Prove2me | Theorems.Thm_Auto_aux_pairwise_square_rpow_le_lintegral
-- name    : Auto.aux_pairwise_square_rpow_le_lintegral
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:40:28.779673+00:00
-- url     : https://prove2.me/theorems/8e52ebc8-4f64-4c50-bebe-29a2e859a1dd
-- title:
--   Auto: aux pairwise square rpow le lintegral
-- statement:
--   Restate the pairwise bound with real `rpow` exponent notation.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L1042-L1048
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L1042-L1048

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem Auto.aux_pairwise_square_rpow_le_lintegral {α β x y : ℝ} (a : ℝ → ℝ)
    (ha : ContDiffOn ℝ 1 a (Set.Icc α β))
    (hx : x ∈ Set.Icc α β) (hy : y ∈ Set.Icc α β) (hxy : x ≤ y) :
    ‖a y - a x‖ₑ ^ (2 : ℝ) ≤
      8 * ∫⁻ z in Set.Ioc x y, ‖a z‖ₑ * ‖deriv a z‖ₑ := by sorry
