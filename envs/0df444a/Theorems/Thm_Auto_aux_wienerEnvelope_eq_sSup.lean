-- Prove2me | Theorems.Thm_Auto_aux_wienerEnvelope_eq_sSup
-- name    : Auto.aux_wienerEnvelope_eq_sSup
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:49:57.809647+00:00
-- url     : https://prove2.me/theorems/ac87b8d2-e075-4ada-8d5d-8be1e7f7101e
-- title:
--   Auto: aux wiener Envelope eq s Sup
-- statement:
--   `wienerEnvelope` is precisely the supremum in the definition from the draft.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L57-L70
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L57-L70

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_wienerEnvelope_eq_sSup {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {f : E → F} {r : ℝ} {x : E} :
    wienerEnvelope f r x = sSup ((fun y : E ↦ ‖f y‖) '' closedBall x r) := by sorry
