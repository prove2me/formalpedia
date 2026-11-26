-- Prove2me | Theorems.Thm_Auto_aux_eLpNorm_toReal_le_of_l1_linf_bounds
-- name    : Auto.aux_eLpNorm_toReal_le_of_l1_linf_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:48:08.280589+00:00
-- url     : https://prove2.me/theorems/7dbadec5-c9f1-4f69-97f2-9a7304ef8fba
-- title:
--   Auto: aux e Lp Norm to Real le of l1 linf bounds
-- statement:
--   The real-valued form of the preceding estimate.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1236-L1255
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1236-L1255

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_eLpNorm_toReal_le_of_l1_linf_bounds
    {E 𝕜 : Type*} [MeasurableSpace E] [NormedAddCommGroup 𝕜] {μ : Measure E}
    {f : E → 𝕜} (hf : AEStronglyMeasurable f μ) {q : ℝ} (hq : 1 ≤ q)
    {A B : ℝ} (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : eLpNorm f 1 μ ≤ ENNReal.ofReal A)
    (hB : eLpNorm f ∞ μ ≤ ENNReal.ofReal B) :
    (eLpNorm f (ENNReal.ofReal q) μ).toReal ≤ A ^ q⁻¹ * B ^ (1 - q⁻¹) := by sorry
