-- Prove2me | Theorems.Thm_D1Bound5_frontier_large_bilinear_bound
-- name    : D1Bound5.frontier_large_bilinear_bound
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:13:20.06111+00:00
-- url     : https://prove2.me/theorems/dcf7735c-c764-4217-82b5-389d8fb9c394
-- title:
--   Frontier large bilinear bound
-- statement:
--   Coordinate bounds for a very unbalanced four-variable bilinear form. The exact coefficient is 88139/270000, strictly below one third.
-- source:
--   D1Bound5/FrontierLargeNumeric.lean, lines 8-48, SHA-256 4bc5dd1e28ae7aa2a88637fecb028683507017fa8e74be43465c456295d143f5. Project: https://github.com/tomislav-math/d1-bound5-lean

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
open scoped NumberField Matrix.Norms.L2Operator BigOperators
open Matrix Module

namespace D1Bound5


theorem _root_.D1Bound5.frontier_large_bilinear_bound
    (G : Matrix (Fin 4) (Fin 4) ℂ) (w : Fin 4 → ℂ) (D : ℝ)
    (hD : 0 ≤ D)
    (hG : ∀ i j, ‖G i j‖ ≤
      if i = j then (273/1000 : ℝ) else (1447/10000 : ℝ))
    (hw : ∀ i, i ≠ 3 → ‖w i‖ ≤ D/18) (hw3 : ‖w 3‖ = D) :
    ‖w ⬝ᵥ (G *ᵥ w)‖ ≤ (88139/270000 : ℝ)*D^2 := by sorry



end D1Bound5
end
