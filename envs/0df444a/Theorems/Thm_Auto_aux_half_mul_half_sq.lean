-- Prove2me | Theorems.Thm_Auto_aux_half_mul_half_sq
-- name    : Auto.aux_half_mul_half_sq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:39:49.006258+00:00
-- url     : https://prove2.me/theorems/0ffb9802-2930-4988-9c8d-e2925ab10ac7
-- title:
--   Auto: aux half mul half sq
-- statement:
--   Squaring a product of two square roots in `ℝ≥0∞`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L711-L716
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L711-L716

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem Auto.aux_half_mul_half_sq (C E : ℝ≥0∞) :
    (C ^ ((2 : ℝ)⁻¹) * E ^ ((2 : ℝ)⁻¹)) ^ (2 : ℝ) = C * E := by sorry
