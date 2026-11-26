-- Prove2me | Theorems.Thm_Auto_aux_cauchy_lintegral_two
-- name    : Auto.aux_cauchy_lintegral_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:39:53.309148+00:00
-- url     : https://prove2.me/theorems/b8445787-5df0-5229-b41c-6fdaf9cf70b8
-- title:
--   Auto: aux cauchy lintegral two
-- statement:
--   The `L¹`--`L²` Cauchy--Schwarz estimate on an arbitrary measure.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L699-L708
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L699-L708

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem Auto.aux_cauchy_lintegral_two {mu : Measure ℝ} {f : ℝ → ℝ≥0∞}
    (hf : AEMeasurable f mu) :
    ∫⁻ t, f t ∂mu ≤ (∫⁻ t, f t ^ (2 : ℝ) ∂mu) ^ ((2 : ℝ)⁻¹) *
      (mu Set.univ) ^ ((2 : ℝ)⁻¹) := by sorry
