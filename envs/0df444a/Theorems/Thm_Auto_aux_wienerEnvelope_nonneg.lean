-- Prove2me | Theorems.Thm_Auto_aux_wienerEnvelope_nonneg
-- name    : Auto.aux_wienerEnvelope_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:42:26.646621+00:00
-- url     : https://prove2.me/theorems/3c358fbd-3ec5-4f09-90a6-151573d66605
-- title:
--   Auto: aux wiener Envelope nonneg
-- statement:
--   A local supremum is nonnegative when its ball is nonempty.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L242-L252
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L242-L252

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_wienerEnvelope_nonneg {E F : Type*} [NormedAddCommGroup E] [ProperSpace E]
    [NormedAddCommGroup F] {f : E → F} (hf : Continuous f) {r : ℝ} (hr : 0 ≤ r) (x : E) :
    0 ≤ wienerEnvelope f r x := by sorry
