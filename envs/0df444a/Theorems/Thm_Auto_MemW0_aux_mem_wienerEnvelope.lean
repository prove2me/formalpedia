-- Prove2me | Theorems.Thm_Auto_MemW0_aux_mem_wienerEnvelope
-- name    : Auto.MemW0.aux_mem_wienerEnvelope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:50:41.931661+00:00
-- url     : https://prove2.me/theorems/627e05dd-ffbf-58e2-8dec-91a7a0764ab9
-- title:
--   Mem W0: aux mem wiener Envelope
-- statement:
--   Positive-radius local envelopes of a Wiener-space function are themselves in `W₀`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L781-L792
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L781-L792

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.MemW0.aux_mem_wienerEnvelope {E F : Type*} [NormedAddCommGroup E] [ProperSpace E]
    [MeasureSpace E] [BorelSpace E] [Measure.IsAddRightInvariant (volume : Measure E)]
    [NormedAddCommGroup F] {f : E → F} (hf : MemW0 f) {r : ℝ} (hr : 0 ≤ r) :
    MemW0 (wienerEnvelope f r) := by sorry
