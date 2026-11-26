-- Prove2me | Theorems.Thm_Auto_MemW0_aux_mem_wienerEnvelope_prod
-- name    : Auto.MemW0.aux_mem_wienerEnvelope_prod
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:43:32.510657+00:00
-- url     : https://prove2.me/theorems/7934feed-a280-5b82-a9c6-b081db5bda5d
-- title:
--   Mem W0: aux mem wiener Envelope prod
-- statement:
--   Positive-radius local envelopes of a Wiener-space function on a Euclidean product are again
--   in `W₀`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1417-L1428
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1417-L1428

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.MemW0.aux_mem_wienerEnvelope_prod {m l : ℕ} {𝕜 : Type*} [NormedAddCommGroup 𝕜]
    {f : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l) → 𝕜}
    (hf : MemW0 f) {r : ℝ} (hr : 0 ≤ r) :
    MemW0 (wienerEnvelope f r) := by sorry
