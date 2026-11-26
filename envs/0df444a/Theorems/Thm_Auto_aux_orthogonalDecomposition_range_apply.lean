-- Prove2me | Theorems.Thm_Auto_aux_orthogonalDecomposition_range_apply
-- name    : Auto.aux_orthogonalDecomposition_range_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:45:04.860232+00:00
-- url     : https://prove2.me/theorems/63d02023-a48f-5482-8f0c-886da9cdf5ea
-- title:
--   Auto: aux orthogonal Decomposition range apply
-- statement:
--   In the orthogonal coordinates associated to the range of a linear map, a point in that
--   range has zero orthogonal component.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L467-L489
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L467-L489

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_orthogonalDecomposition_range_apply {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (π : E →L[ℝ] F) (x : E) :
    let s : Submodule ℝ F := π.range
    let e : F ≃L[ℝ] s × sᗮ :=
      s.orthogonalDecomposition.toContinuousLinearEquiv.trans
        (WithLp.prodContinuousLinearEquiv 2 ℝ s sᗮ)
    e (π x) = (π.rangeRestrict x, 0) := by sorry
