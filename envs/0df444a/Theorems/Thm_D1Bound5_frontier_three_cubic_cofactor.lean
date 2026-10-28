-- Prove2me | Theorems.Thm_D1Bound5_frontier_three_cubic_cofactor
-- name    : D1Bound5.frontier_three_cubic_cofactor
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:33:47.808768+00:00
-- url     : https://prove2.me/theorems/77d03ddb-87bc-4edd-871c-79d374291531
-- title:
--   Frontier three cubic cofactor
-- statement:
--   The three signed cubic cofactor terms cancel at the leading level. Retaining this cancellation gives 3K-1/4 instead of the weaker 3K.
-- source:
--   D1Bound5/FrontierCubicErrors.lean, lines 49-62, SHA-256 290e56b9252013e634702a589994a6103f69a633748ac8b55583e58d2275eedb. Project: https://github.com/tomislav-math/d1-bound5-lean

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
namespace D1Bound5




theorem _root_.D1Bound5.frontier_three_cubic_cofactor (p q r : ℂ) (K : ℝ)
    (hp : ‖p-(1/8 : ℂ)‖ ≤ K-1/8)
    (hq : ‖q-(1/8 : ℂ)‖ ≤ K-1/8)
    (hr : ‖r-(1/8 : ℂ)‖ ≤ K-1/8) :
    ‖p-q-r‖ ≤ 3*K-1/4 := by sorry



end D1Bound5
end
