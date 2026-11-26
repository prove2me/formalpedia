-- Prove2me | Theorems.Thm_Auto_aux_eLpNorm_interpolation_one_top_of_one_le
-- name    : Auto.aux_eLpNorm_interpolation_one_top_of_one_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:48:00.677371+00:00
-- url     : https://prove2.me/theorems/7a5e894b-7a6e-5655-ba08-5067815e8973
-- title:
--   Auto: aux e Lp Norm interpolation one top of one le
-- statement:
--   Quantitative `L¹`--`L∞` interpolation, including the endpoint `q = 1`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1207-L1214
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1207-L1214

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_eLpNorm_interpolation_one_top_of_one_le
    {E 𝕜 : Type*} [MeasurableSpace E] [NormedAddCommGroup 𝕜] {μ : Measure E}
    {f : E → 𝕜} (hf : AEStronglyMeasurable f μ) {q : ℝ} (hq : 1 ≤ q) :
    eLpNorm f (ENNReal.ofReal q) μ ≤
      (eLpNorm f 1 μ) ^ q⁻¹ * (eLpNorm f ∞ μ) ^ (1 - q⁻¹) := by sorry
