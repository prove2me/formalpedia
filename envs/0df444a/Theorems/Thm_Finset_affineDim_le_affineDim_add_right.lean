-- Prove2me | Theorems.Thm_Finset_affineDim_le_affineDim_add_right
-- name    : Finset.affineDim_le_affineDim_add_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:05:45.213282+00:00
-- url     : https://prove2.me/theorems/661ecc33-dacf-53a5-8b1c-becb8c63fee0
-- title:
--   Finset: affine Dim le affine Dim add right
-- statement:
--   The affine dimension of `A` is at most that of `A + B` when `B` is nonempty.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/AffineDimSumset.lean#L37-L44
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/AffineDimSumset.lean#L37-L44

module
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDim
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDimSumset
set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped Pointwise
variable {D : ℕ}

theorem Finset.affineDim_le_affineDim_add_right (A : Finset (Fin D → ℝ))
    {B : Finset (Fin D → ℝ)} (hB : B.Nonempty) : A.affineDim ≤ (A + B).affineDim := by sorry
