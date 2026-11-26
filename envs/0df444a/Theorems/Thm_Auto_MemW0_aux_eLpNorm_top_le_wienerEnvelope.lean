-- Prove2me | Theorems.Thm_Auto_MemW0_aux_eLpNorm_top_le_wienerEnvelope
-- name    : Auto.MemW0.aux_eLpNorm_top_le_wienerEnvelope
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:48:27.63318+00:00
-- url     : https://prove2.me/theorems/e2aef8e4-0cc1-54ae-bf9a-68652416e936
-- title:
--   Mem W0: aux e Lp Norm top le wiener Envelope
-- statement:
--   The quantitative `L∞` endpoint in the Wiener-space estimate.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1306-L1311
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1306-L1311

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.MemW0.aux_eLpNorm_top_le_wienerEnvelope {d : ℕ} {𝕜 : Type*} [NormedAddCommGroup 𝕜]
    {f : EuclideanSpace ℝ (Fin d) → 𝕜} (hf : MemW0 f) :
    eLpNorm f ∞ volume ≤ ENNReal.ofReal ((∫ x, wienerEnvelope f 1 x) /
      volume.real (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)) := by sorry
