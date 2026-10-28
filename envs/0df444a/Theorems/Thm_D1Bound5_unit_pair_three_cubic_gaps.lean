-- Prove2me | Theorems.Thm_D1Bound5_unit_pair_three_cubic_gaps
-- name    : D1Bound5.unit_pair_three_cubic_gaps
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:37:31.24372+00:00
-- url     : https://prove2.me/theorems/e53777e1-7a88-45d8-8667-eddf08e8a193
-- title:
--   Unit pair three cubic gaps
-- statement:
--   Three unit cubic gaps have the exact accumulated denominator 2^13.
-- source:
--   D1Bound5/UnitPairCubicIteration.lean, lines 9-19, SHA-256 a34fce4fbc0641e3fd4321f40ebb3bba4fb6d40eab6d0dad17f09e677f1ee8f7. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
open scoped NumberField
open Module

namespace D1Bound5


theorem _root_.D1Bound5.unit_pair_three_cubic_gaps (S T C D : ℝ) (hS : 9 ≤ S)
    (hST : S^3/2 < T) (hTC : T^3/2 < C) (hCD : C^3/2 < D) :
    S^27/8192 < D := by sorry



end D1Bound5
end
