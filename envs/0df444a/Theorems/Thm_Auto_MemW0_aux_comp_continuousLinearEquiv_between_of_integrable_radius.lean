-- Prove2me | Theorems.Thm_Auto_MemW0_aux_comp_continuousLinearEquiv_between_of_integrable_radius
-- name    : Auto.MemW0.aux_comp_continuousLinearEquiv_between_of_integrable_radius
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:44:07.81633+00:00
-- url     : https://prove2.me/theorems/97520ed7-f4f9-5615-8492-b17c5228e515
-- title:
--   Mem W0: aux comp continuous Linear Equiv between of integrable radius
-- statement:
--   An invertible finite-dimensional linear change of coordinates transports `W₀` after the
--   radius enlargement dictated by its operator norm.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L429-L444
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L429-L444

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.MemW0.aux_comp_continuousLinearEquiv_between_of_integrable_radius {E F K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ProperSpace E]
    [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [ProperSpace F]
    [MeasureSpace F] [BorelSpace F] [Measure.IsAddHaarMeasure (volume : Measure F)]
    [NormedAddCommGroup K] {f : F → K} (hf : MemW0 f) (e : E ≃L[ℝ] F)
    (hr : Integrable (wienerEnvelope f ‖(e : E →L[ℝ] F)‖)) :
    MemW0 (f ∘ e) := by sorry
