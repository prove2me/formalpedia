-- Prove2me | Theorems.Thm_Auto_aux_eLpNorm_toReal_le_interpolation_constant
-- name    : Auto.aux_eLpNorm_toReal_le_interpolation_constant
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:48:10.609109+00:00
-- url     : https://prove2.me/theorems/2514007c-0360-5fbd-930a-3870d79ad7ce
-- title:
--   Auto: aux e Lp Norm to Real le interpolation constant
-- statement:
--   The source-form interpolation estimate after inserting an `L¹` bound `I` and the
--   pointwise bound `I / V`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1286-L1296
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1286-L1296

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_eLpNorm_toReal_le_interpolation_constant
    {E 𝕜 : Type*} [MeasurableSpace E] [NormedAddCommGroup 𝕜] {μ : Measure E}
    {f : E → 𝕜} (hf : AEStronglyMeasurable f μ) {q I V : ℝ} (hq : 1 ≤ q)
    (hI : 0 ≤ I) (hV : 0 < V) (hL1 : eLpNorm f 1 μ ≤ ENNReal.ofReal I)
    (hLinf : eLpNorm f ∞ μ ≤ ENNReal.ofReal (I / V)) :
    (eLpNorm f (ENNReal.ofReal q) μ).toReal ≤ V ^ (q⁻¹ - 1) * I := by sorry
