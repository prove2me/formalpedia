-- Prove2me | Theorems.Thm_Auto_MemW0_aux_comp_linearIsometryEquiv
-- name    : Auto.MemW0.aux_comp_linearIsometryEquiv
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:50:17.432707+00:00
-- url     : https://prove2.me/theorems/dadf0ef5-2a67-474d-99dd-64a0130c2503
-- title:
--   Mem W0: aux comp linear Isometry Equiv
-- statement:
--   Isometric linear equivalences preserve Wiener-space membership.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L361-L373
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L361-L373

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.MemW0.aux_comp_linearIsometryEquiv {E F K : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] [NormedAddCommGroup K]
    {f : F → K} (hf : MemW0 f) (e : E ≃ₗᵢ[ℝ] F) :
    MemW0 (f ∘ e) := by sorry
