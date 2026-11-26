-- Prove2me | Theorems.Thm_Auto_aux_eLpNorm_le_of_l1_linf_bounds
-- name    : Auto.aux_eLpNorm_le_of_l1_linf_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:48:09.056257+00:00
-- url     : https://prove2.me/theorems/5a3fee72-775c-4162-8b58-a59c47701c82
-- title:
--   Auto: aux e Lp Norm le of l1 linf bounds
-- statement:
--   Substituting explicit `L¹` and `L∞` bounds into interpolation.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1217-L1233
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1217-L1233

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_eLpNorm_le_of_l1_linf_bounds
    {E 𝕜 : Type*} [MeasurableSpace E] [NormedAddCommGroup 𝕜] {μ : Measure E}
    {f : E → 𝕜} (hf : AEStronglyMeasurable f μ) {q : ℝ} (hq : 1 ≤ q)
    {A B : ℝ≥0∞} (hA : eLpNorm f 1 μ ≤ A) (hB : eLpNorm f ∞ μ ≤ B) :
    eLpNorm f (ENNReal.ofReal q) μ ≤ A ^ q⁻¹ * B ^ (1 - q⁻¹) := by sorry
