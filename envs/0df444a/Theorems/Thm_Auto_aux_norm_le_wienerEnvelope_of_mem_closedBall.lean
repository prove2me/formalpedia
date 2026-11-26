-- Prove2me | Theorems.Thm_Auto_aux_norm_le_wienerEnvelope_of_mem_closedBall
-- name    : Auto.aux_norm_le_wienerEnvelope_of_mem_closedBall
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:42:30.146576+00:00
-- url     : https://prove2.me/theorems/c7838f7a-05e5-4c96-a3dc-e4011350ac34
-- title:
--   Auto: aux norm le wiener Envelope of mem closed Ball
-- statement:
--   Any point in the ball defining the envelope is bounded by that envelope.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L265-L275
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L265-L275

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_norm_le_wienerEnvelope_of_mem_closedBall {E F : Type*} [NormedAddCommGroup E]
    [ProperSpace E] [NormedAddCommGroup F] {f : E → F} (hf : Continuous f) {r : ℝ}
    {x y : E} (hy : y ∈ closedBall x r) :
    ‖f y‖ ≤ wienerEnvelope f r x := by sorry
