-- Prove2me | Theorems.Thm_D1Bound5_frontier_mixed_rankOne_upper
-- name    : D1Bound5.frontier_mixed_rankOne_upper
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:34:35.174806+00:00
-- url     : https://prove2.me/theorems/e92e7516-dfbb-4585-bf05-12490e620f41
-- title:
--   Frontier mixed rank One upper
-- statement:
--   The exact integrated-four-entry bound before division by ABST. This retains the leading cubic cancellation in off-diagonal cofactors.
-- source:
--   D1Bound5/FrontierMixedDeterminant.lean, lines 42-90, SHA-256 8971d5daa3b2a953daf0d876b723a6ea463e6a13433a1770a4414d8aa48c3133. Project: https://github.com/tomislav-math/d1-bound5-lean

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
open scoped NumberField Matrix.Norms.L2Operator BigOperators
open Matrix Module

namespace D1Bound5




theorem _root_.D1Bound5.frontier_mixed_rankOne_upper
    (F : Matrix (Fin 4) (Fin 4) ℂ) (w : Fin 4 → ℂ) (K Q : ℝ)
    (hF : F.det ≠ 0) (hdet : ‖F.det‖ ≤ Q)
    (hG : ∀ i j, ‖F.adjugate i j‖ ≤ if i = j then 2*K else 3*K-1/4) :
    ‖(F+Matrix.vecMulVec w w).det‖ ≤
      2*K*(‖w 0‖^2+‖w 1‖^2+‖w 2‖^2+‖w 3‖^2)+
      (6*K-1/2)*(‖w 0‖*‖w 1‖+‖w 0‖*‖w 2‖+‖w 0‖*‖w 3‖+
        ‖w 1‖*‖w 2‖+‖w 1‖*‖w 3‖+‖w 2‖*‖w 3‖)+Q := by sorry

end D1Bound5
end
