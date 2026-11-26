-- Prove2me | Theorems.Thm_Auto_MemW0_aux_memW0_slice_of_addHaar
-- name    : Auto.MemW0.aux_memW0_slice_of_addHaar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:52:51.92541+00:00
-- url     : https://prove2.me/theorems/f36b6cdc-c74e-540b-a01f-7a8924c326ad
-- title:
--   Mem W0: aux mem W0 slice of add Haar
-- statement:
--   The coordinate-slice argument works on arbitrary finite-dimensional real Haar spaces as
--   well.  This form is used for orthogonal range decompositions of an injective map.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1474-L1504
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1474-L1504

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.MemW0.aux_memW0_slice_of_addHaar {E F K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ProperSpace E]
    [MeasureSpace E] [BorelSpace E] [SFinite (volume : Measure E)]
    [Measure.IsAddHaarMeasure (volume : Measure E)]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [ProperSpace F]
    [MeasureSpace F] [BorelSpace F] [SFinite (volume : Measure F)]
    [Measure.IsAddHaarMeasure (volume : Measure F)]
    [NormedAddCommGroup K] {f : E × F → K} (hf : MemW0 f) (u : E) :
    MemW0 (fun v ↦ f (u, v)) := by sorry
