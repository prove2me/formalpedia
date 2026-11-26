-- Prove2me | Theorems.Thm_Auto_aux_eLpNorm_interpolation_one_top_of_one_lt
-- name    : Auto.aux_eLpNorm_interpolation_one_top_of_one_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:47:53.197032+00:00
-- url     : https://prove2.me/theorems/cd29b1ea-f2f6-56dd-8ceb-a4aa2212b373
-- title:
--   Auto: aux e Lp Norm interpolation one top of one lt
-- statement:
--   The elementary interpolation estimate between `L¹` and `L∞`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1148-L1204
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1148-L1204

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_eLpNorm_interpolation_one_top_of_one_lt
    {E 𝕜 : Type*} [MeasurableSpace E] [NormedAddCommGroup 𝕜] {μ : Measure E}
    {f : E → 𝕜} (hf : AEStronglyMeasurable f μ) {q : ℝ} (hq : 1 < q) :
    eLpNorm f (ENNReal.ofReal q) μ ≤
      (eLpNorm f 1 μ) ^ q⁻¹ * (eLpNorm f ∞ μ) ^ (1 - q⁻¹) := by sorry
