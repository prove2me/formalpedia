-- Prove2me | Theorems.Thm_Auto_aux_wienerEnvelope_slice_snd_le_of_mem_closedBall_addHaar
-- name    : Auto.aux_wienerEnvelope_slice_snd_le_of_mem_closedBall_addHaar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:48:41.184836+00:00
-- url     : https://prove2.me/theorems/4ddab7b4-2854-50cd-9dac-c64c765a14cd
-- title:
--   Auto: aux wiener Envelope slice snd le of mem closed Ball add Haar
-- statement:
--   A local envelope on a second-coordinate slice is bounded by the ambient envelope at every
--   nearby second-coordinate point.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1611-L1625
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1611-L1625

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_wienerEnvelope_slice_snd_le_of_mem_closedBall_addHaar {E F K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [ProperSpace F]
    [NormedAddCommGroup K] {f : E × F → K} (hf : Continuous f)
    {v v' : F} (hv' : v' ∈ closedBall v 1) (u : E) :
    wienerEnvelope (fun u => f (u, v)) 1 u ≤ wienerEnvelope f 1 (u, v') := by sorry
