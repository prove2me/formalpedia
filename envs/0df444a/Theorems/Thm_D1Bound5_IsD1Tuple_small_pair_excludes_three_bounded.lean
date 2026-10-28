-- Prove2me | Theorems.Thm_D1Bound5_IsD1Tuple_small_pair_excludes_three_bounded
-- name    : D1Bound5.IsD1Tuple.small_pair_excludes_three_bounded
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:14:35.419986+00:00
-- url     : https://prove2.me/theorems/ee8560a1-1478-46f3-a379-efd4650be706
-- title:
--   Is D1Tuple — small pair excludes three bounded
-- statement:
--   An arbitrary nondegenerate pair of small algebraic integers in an imaginary quadratic full ring cannot have three mutually compatible proper extensions in the closed annulus with radii 3 and 10^550.
-- source:
--   D1Bound5/SmallPairBoundedExtensions.lean, lines 9-52, SHA-256 2d3b593f3dbcd94a91f8cff878c1a07d2b27fd0bfa8ae05c2a4318a604fc5399. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Range
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_SmallExtensionSymmetry_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData10_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData14_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData15_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData21_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData23_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData28_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData30_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData36_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData4_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData6_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData8_Definitions

section
open scoped NumberField Classical
open Module

namespace D1Bound5
open QuadInt


theorem _root_.D1Bound5.IsD1Tuple.small_pair_excludes_three_bounded
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 2 → 𝓞 K) (ha : IsD1Tuple a)
    (hsmall : ∀ i, ‖phi (a i : K)‖ < 3)
    (hnondeg : a 0*a 1+1 ≠ 0)
    (t : Fin 3 → 𝓞 K) (ht : IsD1Tuple t)
    (hproper : ∀ i, ProperCommonExtension {a 0,a 1} (t i))
    (hlarge : ∀ i, 3 ≤ ‖phi (t i : K)‖)
    (hbound : ∀ i, ‖phi (t i : K)‖^2 ≤ (10 : ℝ)^1100) : False := by sorry



end D1Bound5
end
