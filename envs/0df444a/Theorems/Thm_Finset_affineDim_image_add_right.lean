-- Prove2me | Theorems.Thm_Finset_affineDim_image_add_right
-- name    : Finset.affineDim_image_add_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:05:45.824237+00:00
-- url     : https://prove2.me/theorems/abe407f7-64da-5af7-91c2-e01225c7d709
-- title:
--   Finset: affine Dim image add right
-- statement:
--   The affine dimension of `S + c` is that of `S`.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/AffineDim.lean#L95-L97
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/AffineDim.lean#L95-L97

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

theorem Finset.affineDim_image_add_right (c : Fin D → ℝ) (S : Finset (Fin D → ℝ)) :
    (S.image (· + c)).affineDim = S.affineDim := by sorry
