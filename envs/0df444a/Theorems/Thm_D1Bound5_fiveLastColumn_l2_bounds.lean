-- Prove2me | Theorems.Thm_D1Bound5_fiveLastColumn_l2_bounds
-- name    : D1Bound5.fiveLastColumn_l2_bounds
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:31:23.958797+00:00
-- url     : https://prove2.me/theorems/c7200d3b-2359-48e5-88bb-e2ec6c6016c2
-- title:
--   Five Last Column l2 bounds
-- statement:
--   The last-column entry bounds imply the Euclidean estimates in (integrated-4); the norm here is explicitly the L2 vector norm.
-- source:
--   D1Bound5/ProductFiveCompatibleSigns.lean, lines 356-389, SHA-256 7ef326eadce635a2fc8001d19ab9a7846a67febccdcf6d3cfe50963ad72c4cef. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
namespace D1Bound5

















open scoped NumberField
open Module







theorem _root_.D1Bound5.fiveLastColumn_l2_bounds (v : Fin 4 → ℂ)
    (hv : ∀ i, ‖v i - (1/2 : ℂ)‖ < (1/400 : ℝ)) :
    ‖(WithLp.toLp 2 (fun i => v i - (1/2 : ℂ)) : EuclideanSpace ℂ (Fin 4))‖ <
        (1/200 : ℝ) ∧
    ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin 4))‖ < (201/200 : ℝ) := by sorry

end D1Bound5
end
