-- Prove2me | Theorems.Thm_Finset_affineDim_le
-- name    : Finset.affineDim_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:06:03.413796+00:00
-- url     : https://prove2.me/theorems/1935980c-a2a3-4cb8-9c7d-1b4743512823
-- title:
--   Finset: affine Dim le
-- statement:
--   The affine dimension of a subset of `ℝ^D` is at most `D`.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/AffineDim.lean#L71-L72
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/AffineDim.lean#L71-L72

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

theorem Finset.affineDim_le (S : Finset (Fin D → ℝ)) : S.affineDim ≤ D := by sorry
