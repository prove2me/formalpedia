-- Prove2me | Theorems.Thm_Auto_measurable_wienerEnvelope
-- name    : Auto.measurable_wienerEnvelope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:44:55.455387+00:00
-- url     : https://prove2.me/theorems/125c7db4-f5c3-4ab6-be06-d4e07973decb
-- title:
--   Auto: measurable wiener Envelope
-- statement:
--   The measurability conclusion of Proposition `Auto.localSupremumMeasurability`; see
--   localSupremumMeasurability.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L88-L91
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L88-L91

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.measurable_wienerEnvelope {E F : Type*} [NormedAddCommGroup E] [ProperSpace E]
    [NormedAddCommGroup F] [MeasurableSpace E] [BorelSpace E] {f : E → F}
    (hf : Continuous f) (r : ℝ) : Measurable (wienerEnvelope f r) := by sorry
