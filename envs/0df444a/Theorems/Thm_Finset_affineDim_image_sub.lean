-- Prove2me | Theorems.Thm_Finset_affineDim_image_sub
-- name    : Finset.affineDim_image_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:06:37.402905+00:00
-- url     : https://prove2.me/theorems/84e0f3bb-81b9-4652-a5bd-091ad013c53e
-- title:
--   Finset: affine Dim image sub
-- statement:
--   The affine dimension of `S - c` is that of `S`.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/AffineDim.lean#L100-L102
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/AffineDim.lean#L100-L102

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

theorem Finset.affineDim_image_sub (S : Finset (Fin D → ℝ)) (c : Fin D → ℝ) :
    (S.image fun x ↦ x - c).affineDim = S.affineDim := by sorry
