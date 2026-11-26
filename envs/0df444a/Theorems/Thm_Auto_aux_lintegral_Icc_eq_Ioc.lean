-- Prove2me | Theorems.Thm_Auto_aux_lintegral_Icc_eq_Ioc
-- name    : Auto.aux_lintegral_Icc_eq_Ioc
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:40:16.256431+00:00
-- url     : https://prove2.me/theorems/360dbd84-b0fd-43de-89ff-9c93d0cb66b6
-- title:
--   Auto: aux lintegral Icc eq Ioc
-- statement:
--   Endpoint changes have zero Lebesgue mass, so `Icc` and `Ioc` give the
--   same nonnegative integral.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L905-L907
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L905-L907

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem Auto.aux_lintegral_Icc_eq_Ioc (f : ℝ → ℝ≥0∞) (x y : ℝ) :
    (∫⁻ z in Set.Icc x y, f z) = ∫⁻ z in Set.Ioc x y, f z := by sorry
