-- Prove2me | Theorems.Thm_Finset_affineDim_vadd_finset
-- name    : Finset.affineDim_vadd_finset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:05:25.069594+00:00
-- url     : https://prove2.me/theorems/541bb1d4-ed64-5d68-b0f5-6ca57f8968e3
-- title:
--   Finset: affine Dim vadd finset
-- statement:
--   The affine dimension is invariant under translation.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/AffineDim.lean#L84-L87
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/AffineDim.lean#L84-L87

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

theorem Finset.affineDim_vadd_finset (c : Fin D → ℝ) (S : Finset (Fin D → ℝ)) :
    (c +ᵥ S).affineDim = S.affineDim := by sorry
