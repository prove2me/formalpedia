-- Prove2me | Theorems.Thm_Auto_aux_norm_le_integral_wienerEnvelope_div_unitClosedBallVolume
-- name    : Auto.aux_norm_le_integral_wienerEnvelope_div_unitClosedBallVolume
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:44:30.850464+00:00
-- url     : https://prove2.me/theorems/2c6e3b82-c0d9-567d-88c7-3c0bfc35f023
-- title:
--   Auto: aux norm le integral wiener Envelope div unit Closed Ball Volume
-- statement:
--   The `L∞` estimate, stated with the (mathlib) Lebesgue volume of the Euclidean unit ball.
--   For positive dimensions this volume is the gamma-function constant displayed in the draft.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1057-L1063
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1057-L1063

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_norm_le_integral_wienerEnvelope_div_unitClosedBallVolume {d : ℕ} {𝕜 : Type*}
    [NormedAddCommGroup 𝕜] {f : EuclideanSpace ℝ (Fin d) → 𝕜} (hf : MemW0 f)
    (x : EuclideanSpace ℝ (Fin d)) :
    ‖f x‖ ≤ (∫ y, wienerEnvelope f 1 y) /
      volume.real (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) := by sorry
