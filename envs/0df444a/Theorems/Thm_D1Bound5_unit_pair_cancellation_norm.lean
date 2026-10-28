-- Prove2me | Theorems.Thm_D1Bound5_unit_pair_cancellation_norm
-- name    : D1Bound5.unit_pair_cancellation_norm
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:33:47.477183+00:00
-- url     : https://prove2.me/theorems/d8184b04-aa93-4e03-bf9a-b971a7ba59fc
-- title:
--   Unit pair cancellation norm
-- statement:
--   The first-order errors cancel exactly in the sum of the two chosen roots; the surviving expression is quadratic in those errors.
-- source:
--   D1Bound5/UnitPairCubic.lean, lines 24-36, SHA-256 16469c8d22e15a9b7e3513551fcffe914102a558214dd99c81069f9bf0bf3a9f. Project: https://github.com/tomislav-math/d1-bound5-lean

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




theorem _root_.D1Bound5.unit_pair_cancellation_norm (u v z w : ℂ)
    (hu : u^2 = z^2+w) (hv : v^2 = z^2-w) :
    2*‖z‖*‖u+v-2*z‖ ≤ ‖u-z‖^2+‖v-z‖^2 := by sorry









end D1Bound5
end
