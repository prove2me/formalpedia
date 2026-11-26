-- Prove2me | Theorems.Thm_Auto_aux_wienerEnvelope_wienerEnvelope_le
-- name    : Auto.aux_wienerEnvelope_wienerEnvelope_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:45:13.330997+00:00
-- url     : https://prove2.me/theorems/e1c5b451-1c14-5bd0-b6e0-da12ae94bcff
-- title:
--   Auto: aux wiener Envelope wiener Envelope le
-- statement:
--   Taking a local envelope twice is bounded by taking one envelope at the sum of the radii.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L492-L517
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L492-L517

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_wienerEnvelope_wienerEnvelope_le {E F : Type*} [NormedAddCommGroup E] [ProperSpace E]
    [NormedAddCommGroup F] {f : E → F} (hf : Continuous f) {r s : ℝ} (hr : 0 ≤ r)
    (hs : 0 ≤ s) (x : E) :
    wienerEnvelope (wienerEnvelope f r) s x ≤ wienerEnvelope f (r + s) x := by sorry
