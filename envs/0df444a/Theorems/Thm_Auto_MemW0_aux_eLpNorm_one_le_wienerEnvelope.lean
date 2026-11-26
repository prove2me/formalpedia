-- Prove2me | Theorems.Thm_Auto_MemW0_aux_eLpNorm_one_le_wienerEnvelope
-- name    : Auto.MemW0.aux_eLpNorm_one_le_wienerEnvelope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:48:23.5818+00:00
-- url     : https://prove2.me/theorems/09f96035-cf04-5ef8-98e7-a9fd48539a16
-- title:
--   Mem W0: aux e Lp Norm one le wiener Envelope
-- statement:
--   The quantitative `L¹` endpoint in the Wiener-space estimate.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1299-L1303
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1299-L1303

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.MemW0.aux_eLpNorm_one_le_wienerEnvelope {d : ℕ} {𝕜 : Type*} [NormedAddCommGroup 𝕜]
    {f : EuclideanSpace ℝ (Fin d) → 𝕜} (hf : MemW0 f) :
    eLpNorm f 1 volume ≤ ENNReal.ofReal (∫ x, wienerEnvelope f 1 x) := by sorry
