-- Prove2me | Theorems.Thm_D1Bound5_IsD1Tuple_tail_irregular_and_growth
-- name    : D1Bound5.IsD1Tuple.tail_irregular_and_growth
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:36:45.96471+00:00
-- url     : https://prove2.me/theorems/0aae3c2d-d14b-406e-896d-d4a6aab50659
-- title:
--   Is D1Tuple — tail irregular and growth
-- statement:
--   Complete tail-irregularity and growth lemma, without the auxiliary C>=4 restriction. Every zero-square, half-integral, and modulus-tie case remains.
-- source:
--   D1Bound5/TailIrregular.lean, lines 65-84, SHA-256 98aee920c9839181f5a78733c62a31450435bbb6574947c82f20fe99ca99dcdd. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_Regular_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5




theorem _root_.D1Bound5.IsD1Tuple.tail_irregular_and_growth
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (t : Fin 4 → 𝓞 K) (ht : IsD1Tuple t)
    (hmon : Monotone (fun i => ‖phi (t i : K)‖))
    (hB : 3 ≤ ‖phi (t 1 : K)‖) :
    regularDefect (t 1) (t 2) (t 3) ≠ 0 ∧
      2*‖phi (t 1 : K)‖*‖phi (t 2 : K)‖ < ‖phi (t 3 : K)‖ := by sorry

end D1Bound5
end
