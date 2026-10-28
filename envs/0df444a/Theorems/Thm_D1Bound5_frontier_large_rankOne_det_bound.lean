-- Prove2me | Theorems.Thm_D1Bound5_frontier_large_rankOne_det_bound
-- name    : D1Bound5.frontier_large_rankOne_det_bound
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:36:58.388434+00:00
-- url     : https://prove2.me/theorems/f0297435-9500-466a-b523-4819c10a66c4
-- title:
--   Frontier large rank One det bound
-- statement:
--   The entrywise adjugate estimate sharpens the previous product-four constant two to three after the already-proved first growth step.
-- source:
--   D1Bound5/FrontierLargeNumeric.lean, lines 50-71, SHA-256 4bc5dd1e28ae7aa2a88637fecb028683507017fa8e74be43465c456295d143f5. Project: https://github.com/tomislav-math/d1-bound5-lean

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




theorem _root_.D1Bound5.frontier_large_rankOne_det_bound
    (F : Matrix (Fin 4) (Fin 4) ℂ) (w : Fin 4 → ℂ) (D : ℝ)
    (hD : 54 ≤ D) (hF : F.det ≠ 0) (hdet : ‖F.det‖ < (1/4 : ℝ))
    (hG : ∀ i j, ‖F.adjugate i j‖ ≤
      if i = j then (273/1000 : ℝ) else (1447/10000 : ℝ))
    (hw : ∀ i, i ≠ 3 → ‖w i‖ ≤ D/18) (hw3 : ‖w 3‖ = D) :
    ‖(F+Matrix.vecMulVec w w).det‖ < D^2/3 := by sorry

end D1Bound5
end
