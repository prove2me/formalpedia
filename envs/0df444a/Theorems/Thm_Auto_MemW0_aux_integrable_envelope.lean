-- Prove2me | Theorems.Thm_Auto_MemW0_aux_integrable_envelope
-- name    : Auto.MemW0.aux_integrable_envelope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:44:05.890543+00:00
-- url     : https://prove2.me/theorems/4914bfbd-5e0e-49d4-95e6-e21033e57bda
-- title:
--   Mem W0: aux integrable envelope
-- statement:
--   The Mem W0 construction uses the aux integrable envelope property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L237-L239
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L237-L239

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.MemW0.aux_integrable_envelope {E 𝕜 : Type*} [NormedAddCommGroup E] [MeasureSpace E]
    [NormedAddCommGroup 𝕜] {f : E → 𝕜} (hf : MemW0 f) : Integrable (wienerEnvelope f 1) := by sorry
