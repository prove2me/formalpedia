-- Prove2me | Theorems.Thm_D1Bound5_IsD1Tuple_one_small_first_triple_classification
-- name    : D1Bound5.IsD1Tuple.one_small_first_triple_classification
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:55:53.61332+00:00
-- url     : https://prove2.me/theorems/1ecc56e2-a0f8-4553-8b8d-b13fcb57abab
-- title:
--   Is D1Tuple — one small first triple classification
-- statement:
--   Complete actual-full-ring classification after the analytic first-pair and third-entry size reductions. Only the rational pair remains separate.
-- source:
--   D1Bound5/OneSmallFullRingFinite.lean, lines 9-47, SHA-256 c38fd48e9b736d57c9245c63903e03393e9c506b12b4772b6531ad1bbd5204fe. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_OneSmallRows_Definitions
import Definitions.Def_D1Bound5_OneSmallSymmetry_Definitions
import Definitions.Def_D1Bound5_SmallPairClassification_Definitions

section
open scoped NumberField Classical
open Module

namespace D1Bound5
open QuadInt


theorem _root_.D1Bound5.IsD1Tuple.one_small_first_triple_classification
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (t : Fin 3 → 𝓞 K) (ht : IsD1Tuple t)
    (hsize :
      (‖phi (t 0 : K)‖^2 = 1 ∧ 9 ≤ ‖phi (t 1 : K)‖^2 ∧ ‖phi (t 1 : K)‖^2 < 64) ∨
      (‖phi (t 0 : K)‖^2 = 2 ∧ 9 ≤ ‖phi (t 1 : K)‖^2 ∧ ‖phi (t 1 : K)‖^2 < 16))
    (hbound : ‖phi (t 2 : K)‖^2 < 225)
    (horder : ‖phi (t 1 : K)‖^2 ≤ ‖phi (t 2 : K)‖^2) :
    (t 0 = 1 ∧ t 1 = 3) ∨ (t 0 = -1 ∧ t 1 = -3) ∨
      ∃ (tau nu : ℤ) (e : QuadInt tau nu ≃+* 𝓞 K),
        (tau,nu) ∈ smallPairModels ∧
        OneSmallNormalizedThirdRows (e.symm (t 0)) (e.symm (t 1)) (e.symm (t 2)) := by sorry





end D1Bound5
end
