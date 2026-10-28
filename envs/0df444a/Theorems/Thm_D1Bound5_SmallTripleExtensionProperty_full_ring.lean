-- Prove2me | Theorems.Thm_D1Bound5_SmallTripleExtensionProperty_full_ring
-- name    : D1Bound5.SmallTripleExtensionProperty.full_ring
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:06:26.028998+00:00
-- url     : https://prove2.me/theorems/5d8b8cf8-6a40-4bf6-a52b-60a8f95ec42c
-- title:
--   Small Triple Extension Property — full ring
-- statement:
--   Transfer both finite-extension consequences from integer coordinates to the actual full ring through its proved ring equivalence.
-- source:
--   D1Bound5/SmallTripleBoundedExtensions.lean, lines 9-44, SHA-256 48c636c065940c264bf5d45a57d236f9488ed0396e76184df898bebb518e4568. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallExtensionSymmetry_Definitions

section
open scoped NumberField Classical
open Module

namespace D1Bound5
open QuadInt


theorem _root_.D1Bound5.SmallTripleExtensionProperty.full_ring
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    {tau nu : ℤ} (e : QuadInt tau nu ≃+* 𝓞 K) (phi : K →+* ℂ)
    (A : Finset (QuadInt tau nu)) (hA : SmallTripleExtensionProperty A) :
    (∀ z : 𝓞 K, ProperCommonExtension (A.image e) z →
      ‖phi (z : K)‖^2 ≤ (10 : ℝ)^80 → ‖phi (z : K)‖ < 85) ∧
    (∀ z w : 𝓞 K, ProperCommonExtension (A.image e) z →
      ProperCommonExtension (A.image e) w →
      ‖phi (z : K)‖^2 ≤ (10 : ℝ)^80 →
      ‖phi (w : K)‖^2 ≤ (10 : ℝ)^80 → z = w) := by sorry



end D1Bound5
end
