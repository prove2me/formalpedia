-- Prove2me | Theorems.Thm_Finset_affineDim_le_affineDim_add_left
-- name    : Finset.affineDim_le_affineDim_add_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:08:39.399664+00:00
-- url     : https://prove2.me/theorems/7f1d210b-8435-5820-9c92-bcc4b0921e04
-- title:
--   Finset: affine Dim le affine Dim add left
-- statement:
--   The affine dimension of `B` is at most that of `A + B` when `A` is nonempty.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/AffineDimSumset.lean#L47-L50
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/AffineDimSumset.lean#L47-L50

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

theorem Finset.affineDim_le_affineDim_add_left {A : Finset (Fin D → ℝ)} (hA : A.Nonempty)
    (B : Finset (Fin D → ℝ)) : B.affineDim ≤ (A + B).affineDim := by sorry
