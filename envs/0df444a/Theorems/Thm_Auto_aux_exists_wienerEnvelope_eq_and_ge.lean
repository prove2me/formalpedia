-- Prove2me | Theorems.Thm_Auto_aux_exists_wienerEnvelope_eq_and_ge
-- name    : Auto.aux_exists_wienerEnvelope_eq_and_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:50:00.712518+00:00
-- url     : https://prove2.me/theorems/9bab4344-a443-49e9-a5ae-12e50f0230d4
-- title:
--   Auto: aux exists wiener Envelope eq and ge
-- statement:
--   The supremum defining the envelope is attained on every nonempty closed ball.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L94-L102
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L94-L102

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_exists_wienerEnvelope_eq_and_ge {E F : Type*} [NormedAddCommGroup E] [ProperSpace E]
    [NormedAddCommGroup F] {f : E → F} (hf : Continuous f) {r : ℝ} (hr : 0 ≤ r) (x : E) :
    ∃ z ∈ closedBall (0 : E) r, wienerEnvelope f r x = ‖f (x + z)‖ ∧
      ∀ w ∈ closedBall (0 : E) r, ‖f (x + w)‖ ≤ ‖f (x + z)‖ := by sorry
