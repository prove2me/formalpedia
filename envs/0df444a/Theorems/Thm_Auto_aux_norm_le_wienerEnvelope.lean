-- Prove2me | Theorems.Thm_Auto_aux_norm_le_wienerEnvelope
-- name    : Auto.aux_norm_le_wienerEnvelope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:43:58.695169+00:00
-- url     : https://prove2.me/theorems/f113f49f-c297-50ef-87c0-42477b4a6f85
-- title:
--   Auto: aux norm le wiener Envelope
-- statement:
--   The original function is bounded by every nonempty-radius Wiener envelope.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L255-L262
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L255-L262

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_norm_le_wienerEnvelope {E F : Type*} [NormedAddCommGroup E] [ProperSpace E]
    [NormedAddCommGroup F] {f : E → F} (hf : Continuous f) {r : ℝ} (hr : 0 ≤ r) (x : E) :
    ‖f x‖ ≤ wienerEnvelope f r x := by sorry
