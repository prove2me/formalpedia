-- Prove2me | Theorems.Thm_Auto_aux_integral_wienerEnvelope_slice_snd_le_unitClosedBallVolume_inv_mul_addHaar
-- name    : Auto.aux_integral_wienerEnvelope_slice_snd_le_unitClosedBallVolume_inv_mul_addHaar
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:48:54.448224+00:00
-- url     : https://prove2.me/theorems/188def2f-d3d9-44de-a1a8-ac3b1f37d673
-- title:
--   Auto: aux integral wiener Envelope slice snd le unit Closed Ball Volume inv mul add Haar
-- statement:
--   The Wiener integral of a second-coordinate slice is bounded uniformly by the ambient Wiener
--   integral on an arbitrary finite-dimensional additive Haar product.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1631-L1672
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1631-L1672

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_integral_wienerEnvelope_slice_snd_le_unitClosedBallVolume_inv_mul_addHaar
    {E F K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ProperSpace E]
    [MeasureSpace E] [BorelSpace E] [SFinite (volume : Measure E)]
    [Measure.IsAddHaarMeasure (volume : Measure E)]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [ProperSpace F]
    [MeasureSpace F] [BorelSpace F] [SFinite (volume : Measure F)]
    [Measure.IsAddHaarMeasure (volume : Measure F)]
    [NormedAddCommGroup K] {f : E × F → K} (hf : MemW0 f) (v : F) :
    (∫ u, wienerEnvelope (fun u => f (u, v)) 1 u) ≤
      ((volume : Measure F).real (closedBall 0 1))⁻¹ * ∫ p, wienerEnvelope f 1 p := by sorry
