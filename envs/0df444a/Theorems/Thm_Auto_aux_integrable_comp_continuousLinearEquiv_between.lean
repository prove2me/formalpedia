-- Prove2me | Theorems.Thm_Auto_aux_integrable_comp_continuousLinearEquiv_between
-- name    : Auto.aux_integrable_comp_continuousLinearEquiv_between
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:45:14.124577+00:00
-- url     : https://prove2.me/theorems/4854b727-7c39-461a-a9e2-81f48b12d699
-- title:
--   Auto: aux integrable comp continuous Linear Equiv between
-- statement:
--   Integrability is preserved by an invertible linear change of finite-dimensional Haar
--   coordinates; the Jacobian only rescales the ambient measure by a positive finite constant.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L379-L394
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L379-L394

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_integrable_comp_continuousLinearEquiv_between {E F K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ProperSpace E]
    [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [ProperSpace F]
    [MeasureSpace F] [BorelSpace F] [Measure.IsAddHaarMeasure (volume : Measure F)]
    [NormedAddCommGroup K] {g : F → K} (hg : Integrable g) (e : E ≃L[ℝ] F) :
    Integrable (g ∘ e) := by sorry
