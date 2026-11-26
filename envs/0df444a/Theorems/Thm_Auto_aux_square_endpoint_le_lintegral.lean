-- Prove2me | Theorems.Thm_Auto_aux_square_endpoint_le_lintegral
-- name    : Auto.aux_square_endpoint_le_lintegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:40:01.84782+00:00
-- url     : https://prove2.me/theorems/5d37664a-78de-5e8e-b8a9-bfdfbf0334f3
-- title:
--   Auto: aux square endpoint le lintegral
-- statement:
--   The endpoint estimate for the square of a continuously differentiable
--   function.  This is the common analytic input to the sign-sensitive variation
--   bound below.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L844-L867
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L844-L867

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem Auto.aux_square_endpoint_le_lintegral {α β x y : ℝ} (a : ℝ → ℝ)
    (ha : ContDiffOn ℝ 1 a (Set.Icc α β))
    (hx : x ∈ Set.Icc α β) (hy : y ∈ Set.Icc α β) (hxy : x ≤ y) :
    ‖a y * a y - a x * a x‖ₑ ≤
      ∫⁻ z in Set.Icc x y, (2 : ℝ≥0∞) * ‖a z‖ₑ * ‖deriv a z‖ₑ := by sorry
