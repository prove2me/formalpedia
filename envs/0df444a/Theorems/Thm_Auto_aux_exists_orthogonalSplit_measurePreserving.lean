-- Prove2me | Theorems.Thm_Auto_aux_exists_orthogonalSplit_measurePreserving
-- name    : Auto.aux_exists_orthogonalSplit_measurePreserving
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:50:22.458993+00:00
-- url     : https://prove2.me/theorems/63aa3610-5cba-5cf1-b0d2-a92abf972467
-- title:
--   Auto: aux exists orthogonal Split measure Preserving
-- statement:
--   Orthogonal decomposition gives a measure-preserving linear equivalence from a finite-
--   dimensional inner-product space to a subspace times its orthogonal complement.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L450-L461
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L450-L461

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_exists_orthogonalSplit_measurePreserving {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (s : Submodule ℝ V) :
    ∃ e : V ≃L[ℝ] s × sᗮ, MeasurePreserving e := by sorry
