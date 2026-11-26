-- Prove2me | Theorems.Thm_Auto_aux_norm_mul_unitClosedBallVolume_le_integral_wienerEnvelope
-- name    : Auto.aux_norm_mul_unitClosedBallVolume_le_integral_wienerEnvelope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:47:31.500839+00:00
-- url     : https://prove2.me/theorems/cb2d366c-dbab-58f7-9d30-11326380fcbb
-- title:
--   Auto: aux norm mul unit Closed Ball Volume le integral wiener Envelope
-- statement:
--   A pointwise value is controlled by the Wiener integral times the volume of the unit ball.
--   This is the geometric core of the `L∞` embedding.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1009-L1031
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1009-L1031

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_norm_mul_unitClosedBallVolume_le_integral_wienerEnvelope {d : ℕ} {𝕜 : Type*}
    [NormedAddCommGroup 𝕜] {f : EuclideanSpace ℝ (Fin d) → 𝕜} (hf : MemW0 f)
    (x : EuclideanSpace ℝ (Fin d)) :
    ‖f x‖ * volume.real (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) ≤
      ∫ y, wienerEnvelope f 1 y := by sorry
