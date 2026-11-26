-- Prove2me | Theorems.Thm_Finset_affineDim_eq_finrank_vectorSpan
-- name    : Finset.affineDim_eq_finrank_vectorSpan
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:05:26.364645+00:00
-- url     : https://prove2.me/theorems/22bb4375-6248-5790-b71c-937af2f79daf
-- title:
--   Finset: affine Dim eq finrank vector Span
-- statement:
--   The affine dimension of `S` is the dimension of the vector span of `S`.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/AffineDim.lean#L51-L53
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/AffineDim.lean#L51-L53

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

theorem Finset.affineDim_eq_finrank_vectorSpan (S : Finset (Fin D → ℝ)) :
    S.affineDim = Module.finrank ℝ (vectorSpan ℝ (S : Set (Fin D → ℝ))) := by sorry
