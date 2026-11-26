-- Prove2me | Theorems.Thm_Auto_aux_log_local_integral_eq
-- name    : Auto.aux_log_local_integral_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:39:45.657363+00:00
-- url     : https://prove2.me/theorems/4d72dda1-9d11-5c72-8983-482f20d56daf
-- title:
--   Auto: aux log local integral eq
-- statement:
--   On a positive subinterval, multiplying the derivative by the logarithmic
--   density cancels the displayed factor of `t`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L631-L651
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L631-L651

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem Auto.aux_log_local_integral_eq {α β x y : ℝ} (hα : 0 < α)
    (hx : x ∈ Set.Icc α β) (hy : y ∈ Set.Icc α β) (a : ℝ → ℝ) :
    (∫⁻ t in Set.Icc x y, ‖t * deriv a t‖ₑ ∂aux_logarithmicMeasure α β) =
      ∫⁻ t in Set.Icc x y, ‖deriv a t‖ₑ := by sorry
