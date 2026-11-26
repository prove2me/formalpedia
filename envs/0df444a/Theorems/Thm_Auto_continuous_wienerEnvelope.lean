-- Prove2me | Theorems.Thm_Auto_continuous_wienerEnvelope
-- name    : Auto.continuous_wienerEnvelope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:42:28.886949+00:00
-- url     : https://prove2.me/theorems/8087439f-4be8-5076-aa9d-ea89b77299e7
-- title:
--   Auto: continuous wiener Envelope
-- statement:
--   Auxiliary for Proposition `Auto.localSupremumMeasurability`; it proves the stronger
--   continuity assertion used by localSupremumMeasurability.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L76-L82
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L76-L82

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.continuous_wienerEnvelope {E F : Type*} [NormedAddCommGroup E] [ProperSpace E]
    [NormedAddCommGroup F] {f : E → F} (hf : Continuous f) (r : ℝ) :
    Continuous (wienerEnvelope f r) := by sorry
