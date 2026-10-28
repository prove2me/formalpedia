-- Prove2me | Theorems.Thm_D1Bound5_IsD1Tuple_small_triple_bounded_extensions
-- name    : D1Bound5.IsD1Tuple.small_triple_bounded_extensions
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:52:31.896481+00:00
-- url     : https://prove2.me/theorems/a76fa0b2-e0a9-4ba7-94de-6a3cf129bc45
-- title:
--   Is D1Tuple — small triple bounded extensions
-- statement:
--   Every actual small D(1)-triple has at most one distinct nonzero further common extension in the radius-10^40 disk. Every such extension has modulus strictly less than 85. The classification, symmetries, finite certificates and reversible descent are all supplied by proved dependencies.
-- source:
--   D1Bound5/SmallTripleBoundedExtensions.lean, lines 46-69, SHA-256 48c636c065940c264bf5d45a57d236f9488ed0396e76184df898bebb518e4568. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Group.Int.Units
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
import Mathlib.Data.List.Range
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

section
open scoped NumberField Classical
open Module

namespace D1Bound5
open QuadInt




theorem _root_.D1Bound5.IsD1Tuple.small_triple_bounded_extensions
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (t : Fin 3 → 𝓞 K) (ht : IsD1Tuple t)
    (hsmall : ∀ i, ‖phi (t i : K)‖ < 3) :
    (∀ z : 𝓞 K, ProperCommonExtension {t 0,t 1,t 2} z →
      ‖phi (z : K)‖^2 ≤ (10 : ℝ)^80 → ‖phi (z : K)‖ < 85) ∧
    (∀ z w : 𝓞 K, ProperCommonExtension {t 0,t 1,t 2} z →
      ProperCommonExtension {t 0,t 1,t 2} w →
      ‖phi (z : K)‖^2 ≤ (10 : ℝ)^80 →
      ‖phi (w : K)‖^2 ≤ (10 : ℝ)^80 → z = w) := by sorry

end D1Bound5
end
