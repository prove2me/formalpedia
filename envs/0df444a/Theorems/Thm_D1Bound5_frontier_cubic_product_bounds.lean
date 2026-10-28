-- Prove2me | Theorems.Thm_D1Bound5_frontier_cubic_product_bounds
-- name    : D1Bound5.frontier_cubic_product_bounds
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:36:43.081644+00:00
-- url     : https://prove2.me/theorems/cbe0e907-73b1-41ad-b182-d73d67144e3a
-- title:
--   Frontier cubic product bounds
-- statement:
--   A product of three near-half factors has the exact leading one-eighth and a remainder bounded by the corresponding product of envelopes.
-- source:
--   D1Bound5/FrontierCubicErrors.lean, lines 6-47, SHA-256 290e56b9252013e634702a589994a6103f69a633748ac8b55583e58d2275eedb. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.frontier_cubic_product_bounds (x y z : ℂ) (k l : ℝ)
    (hk : (1/2 : ℝ) ≤ k) (hl : (1/2 : ℝ) ≤ l)
    (hx : ‖x-(1/2 : ℂ)‖ ≤ k-1/2)
    (hy : ‖y-(1/2 : ℂ)‖ ≤ k-1/2)
    (hz : ‖z-(1/2 : ℂ)‖ ≤ l-1/2) :
    ‖x*y*z‖ ≤ k^2*l ∧ ‖x*y*z-(1/8 : ℂ)‖ ≤ k^2*l-1/8 := by sorry





end D1Bound5
end
