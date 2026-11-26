-- Prove2me | Theorems.Thm_Finset_affineDim_image_add_left
-- name    : Finset.affineDim_image_add_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:06:20.459884+00:00
-- url     : https://prove2.me/theorems/ebb6e747-2ae4-4549-972a-366c0f2215d2
-- title:
--   Finset: affine Dim image add left
-- statement:
--   The affine dimension of `c + S` is that of `S`.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/AffineDim.lean#L90-L92
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/AffineDim.lean#L90-L92

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

theorem Finset.affineDim_image_add_left (c : Fin D → ℝ) (S : Finset (Fin D → ℝ)) :
    (S.image (c + ·)).affineDim = S.affineDim := by sorry
