-- Prove2me | Theorems.Thm_Auto_aux_wienerEnvelope_comp_continuousLinearMap_le
-- name    : Auto.aux_wienerEnvelope_comp_continuousLinearMap_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:43:27.441989+00:00
-- url     : https://prove2.me/theorems/82c56511-e4c8-5424-a3d3-2200c7ed1499
-- title:
--   Auto: aux wiener Envelope comp continuous Linear Map le
-- statement:
--   A linear change of variables enlarges a unit local envelope by at most the operator norm of
--   the change of variables.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L293-L313
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L293-L313

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_wienerEnvelope_comp_continuousLinearMap_le {E F K : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] [ProperSpace F]
    [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedAddCommGroup K]
    (e : E →L[ℝ] F) {f : F → K} (hf : Continuous f) (x : E) :
    wienerEnvelope (f ∘ e) 1 x ≤ wienerEnvelope f ‖e‖ (e x) := by sorry
