-- Prove2me | Theorems.Thm_Auto_aux_integral_wienerEnvelope_slice_le_unitClosedBallVolume_inv_mul
-- name    : Auto.aux_integral_wienerEnvelope_slice_le_unitClosedBallVolume_inv_mul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:48:52.233314+00:00
-- url     : https://prove2.me/theorems/511bf62b-5a64-44a1-9187-4a6a046d694b
-- title:
--   Auto: aux integral wiener Envelope slice le unit Closed Ball Volume inv mul
-- statement:
--   A coordinate fibre has a uniform Wiener-integral bound.  Averaging the local envelope over
--   a unit ball in the transverse coordinate repairs the non-uniform supremum-to-average step in the
--   draft's proof.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1809-L1892
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1809-L1892

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_integral_wienerEnvelope_slice_le_unitClosedBallVolume_inv_mul
    {m l : ℕ} {𝕜 : Type*} [NormedAddCommGroup 𝕜]
    {f : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l) → 𝕜}
    (hf : MemW0 f) (u : EuclideanSpace ℝ (Fin m)) :
    (∫ v, wienerEnvelope (fun v => f (u, v)) 1 v) ≤
      (volume.real (closedBall (0 : EuclideanSpace ℝ (Fin m)) 1))⁻¹ *
        ∫ p, wienerEnvelope f 1 p := by sorry
