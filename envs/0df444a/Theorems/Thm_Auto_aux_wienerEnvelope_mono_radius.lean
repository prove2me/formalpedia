-- Prove2me | Theorems.Thm_Auto_aux_wienerEnvelope_mono_radius
-- name    : Auto.aux_wienerEnvelope_mono_radius
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:46:34.138802+00:00
-- url     : https://prove2.me/theorems/8125ca19-d07c-580f-b744-fab8d4c370f1
-- title:
--   Auto: aux wiener Envelope mono radius
-- statement:
--   Enlarging the radius can only enlarge the local supremum.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L278-L287
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L278-L287

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_wienerEnvelope_mono_radius {E F : Type*} [NormedAddCommGroup E] [ProperSpace E]
    [NormedAddCommGroup F] {f : E → F} (hf : Continuous f) {r s : ℝ} (hr : 0 ≤ r)
    (hrs : r ≤ s) (x : E) :
    wienerEnvelope f r x ≤ wienerEnvelope f s x := by sorry
