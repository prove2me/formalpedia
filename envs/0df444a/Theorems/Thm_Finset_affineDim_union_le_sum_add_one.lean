-- Prove2me | Theorems.Thm_Finset_affineDim_union_le_sum_add_one
-- name    : Finset.affineDim_union_le_sum_add_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:06:53.716798+00:00
-- url     : https://prove2.me/theorems/75c87e58-976b-5f6b-a5f3-a97cc2fcb964
-- title:
--   Finset: affine Dim union le sum add one
-- statement:
--   The affine span of `A ∪ B` has dimension at most one more than the affine span of `A + B`.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/AffineDimSumset.lean#L76-L85
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/AffineDimSumset.lean#L76-L85

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

theorem Finset.affineDim_union_le_sum_add_one {A B : Finset (Fin D → ℝ)}
    (hA : A.Nonempty) (hB : B.Nonempty) :
    (A ∪ B).affineDim ≤ (A + B).affineDim + 1 := by sorry
