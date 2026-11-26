-- Prove2me | Theorems.Thm_Auto_MemW0_aux_memW0_slice_snd_of_addHaar
-- name    : Auto.MemW0.aux_memW0_slice_snd_of_addHaar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:44:40.001158+00:00
-- url     : https://prove2.me/theorems/bab5b602-b0f4-4df7-9010-3bc51e68fc9b
-- title:
--   Mem W0: aux mem W0 slice snd of add Haar
-- statement:
--   The symmetric version of `MemW0.aux_memW0_slice_of_addHaar`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1507-L1537
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1507-L1537

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.MemW0.aux_memW0_slice_snd_of_addHaar {E F K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ProperSpace E]
    [MeasureSpace E] [BorelSpace E] [SFinite (volume : Measure E)]
    [Measure.IsAddHaarMeasure (volume : Measure E)]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [ProperSpace F]
    [MeasureSpace F] [BorelSpace F] [SFinite (volume : Measure F)]
    [Measure.IsAddHaarMeasure (volume : Measure F)]
    [NormedAddCommGroup K] {f : E × F → K} (hf : MemW0 f) (v : F) :
    MemW0 (fun u ↦ f (u, v)) := by sorry
