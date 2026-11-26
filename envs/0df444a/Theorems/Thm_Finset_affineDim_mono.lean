-- Prove2me | Theorems.Thm_Finset_affineDim_mono
-- name    : Finset.affineDim_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:05:43.837382+00:00
-- url     : https://prove2.me/theorems/6387fcda-7d97-5db7-a90b-9a8df3201e96
-- title:
--   Finset: affine Dim mono
-- statement:
--   Affine dimension is monotone under inclusion of finite sets.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/AffineDim.lean#L62-L68
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/AffineDim.lean#L62-L68

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

theorem Finset.affineDim_mono {S T : Finset (Fin D → ℝ)}
    (hST : S ⊆ T) : S.affineDim ≤ T.affineDim := by sorry
