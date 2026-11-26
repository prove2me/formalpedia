-- Prove2me | Theorems.Thm_Finset_affineDim_empty
-- name    : Finset.affineDim_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:05:25.618254+00:00
-- url     : https://prove2.me/theorems/65668c04-45e8-58ac-b404-526a6ed91932
-- title:
--   Finset: affine Dim empty
-- statement:
--   The Finset construction uses the affine Dim empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/AffineDim.lean#L75-L76
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/AffineDim.lean#L75-L76

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

theorem Finset.affineDim_empty : (∅ : Finset (Fin D → ℝ)).affineDim = 0 := by sorry
