-- Prove2me | Theorems.Thm_Finset_affineDim_add_eq_of_left_eq
-- name    : Finset.affineDim_add_eq_of_left_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:05:42.774331+00:00
-- url     : https://prove2.me/theorems/8572341f-3aff-50ad-acdd-eef7ba20f307
-- title:
--   Finset: affine Dim add eq of left eq
-- statement:
--   If `A ⊆ ℝ^D` has affine dimension `D` and `B` is nonempty, then `A + B` has affine
--   dimension `D`.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/AffineDimSumset.lean#L54-L57
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/AffineDimSumset.lean#L54-L57

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

theorem Finset.affineDim_add_eq_of_left_eq {A B : Finset (Fin D → ℝ)} (hB : B.Nonempty)
    (hA : A.affineDim = D) : (A + B).affineDim = D := by sorry
