-- Prove2me | Theorems.Thm_Auto_upperSemicontinuous_wienerEnvelope
-- name    : Auto.upperSemicontinuous_wienerEnvelope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:46:25.174202+00:00
-- url     : https://prove2.me/theorems/c65eb19a-f72e-55b6-aa96-a2ed80b2e0df
-- title:
--   Auto: upper Semicontinuous wiener Envelope
-- statement:
--   The upper-semicontinuity conclusion of Proposition `Auto.localSupremumMeasurability`;
--   see localSupremumMeasurability.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L108-L111
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L108-L111

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.upperSemicontinuous_wienerEnvelope {E F : Type*} [NormedAddCommGroup E] [ProperSpace E]
    [NormedAddCommGroup F] {f : E → F} (hf : Continuous f) (r : ℝ) :
    UpperSemicontinuous (wienerEnvelope f r) := by sorry
