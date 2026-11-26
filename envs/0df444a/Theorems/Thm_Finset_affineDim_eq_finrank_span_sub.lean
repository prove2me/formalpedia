-- Prove2me | Theorems.Thm_Finset_affineDim_eq_finrank_span_sub
-- name    : Finset.affineDim_eq_finrank_span_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:05:40.916129+00:00
-- url     : https://prove2.me/theorems/426e5e5f-bde7-5e01-9bed-08cbebd86513
-- title:
--   Finset: affine Dim eq finrank span sub
-- statement:
--   The affine dimension of `S` is the dimension of the span of `S - S`.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/AffineDim.lean#L56-L59
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/AffineDim.lean#L56-L59

module
public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDim
set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped Pointwise
variable {D : ℕ}

theorem Finset.affineDim_eq_finrank_span_sub (S : Finset (Fin D → ℝ)) :
    S.affineDim = Module.finrank ℝ (Submodule.span ℝ (↑S - ↑S : Set (Fin D → ℝ))) := by sorry
