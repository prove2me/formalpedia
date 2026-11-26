-- Prove2me | Theorems.Thm_Finset_affineDim_add_one_le_card
-- name    : Finset.affineDim_add_one_le_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:05:41.975114+00:00
-- url     : https://prove2.me/theorems/3a4d9485-7e3c-5b51-942c-b5198fbd7502
-- title:
--   Finset: affine Dim add one le card
-- statement:
--   A nonempty finite set of affine dimension `d` contains at least `d + 1` points.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/AffineDim.lean#L105-L110
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/AffineDim.lean#L105-L110

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

theorem Finset.affineDim_add_one_le_card {S : Finset (Fin D → ℝ)} (hS : S.Nonempty) :
    S.affineDim + 1 ≤ #S := by sorry
