-- Prove2me | Theorems.Thm_Finset_affineDim_le_card
-- name    : Finset.affineDim_le_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:08:36.918305+00:00
-- url     : https://prove2.me/theorems/cba3de82-a30e-4d9b-af0b-c1e8d29108e9
-- title:
--   Finset: affine Dim le card
-- statement:
--   The affine dimension of a finite set is at most its number of points.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/AffineDim.lean#L113-L116
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/AffineDim.lean#L113-L116

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

theorem Finset.affineDim_le_card (S : Finset (Fin D → ℝ)) : S.affineDim ≤ #S := by sorry
