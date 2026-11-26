-- Prove2me | Theorems.Thm_Auto_MemW0_aux_integrable_wienerEnvelope_slice
-- name    : Auto.MemW0.aux_integrable_wienerEnvelope_slice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:53:22.931678+00:00
-- url     : https://prove2.me/theorems/a86021b6-2025-4b90-87ee-c7b5b727da0c
-- title:
--   Mem W0: aux integrable wiener Envelope slice
-- statement:
--   The unit-envelope of a Wiener-space function is integrable on every coordinate fibre.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1895-L1900
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1895-L1900

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.MemW0.aux_integrable_wienerEnvelope_slice {m l : ℕ} {𝕜 : Type*}
    [NormedAddCommGroup 𝕜]
    {f : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l) → 𝕜}
    (hf : MemW0 f) (u : EuclideanSpace ℝ (Fin m)) :
    Integrable (fun v ↦ wienerEnvelope f 1 (u, v)) := by sorry
