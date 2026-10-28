-- Prove2me | Theorems.Thm_D1Bound5_frontier_fifteen_numeric
-- name    : D1Bound5.frontier_fifteen_numeric
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:30:07.262717+00:00
-- url     : https://prove2.me/theorems/cd1407b1-d698-4fa7-8400-690e812a2336
-- title:
--   Frontier fifteen numeric
-- statement:
--   Auxiliary result `frontier_fifteen_numeric` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FrontierFifteenNumeric.lean, lines 9-98, SHA-256 3122c98662e60a3fcf8105b6ce6ac200558a87cd3502de98958615f5f2e0f062. Project: https://github.com/tomislav-math/d1-bound5-lean

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
open scoped Matrix.Norms.L2Operator BigOperators
open Matrix

namespace D1Bound5

theorem _root_.D1Bound5.frontier_fifteen_numeric (A B C D : ℝ)
    (hA1 : 1 ≤ A) (hA3 : A < 3) (hB : 3 ≤ B) (hC : 15 ≤ C)
    (hD : 2*B*C < D)
    (hupper : A*B*C*D ≤
      (252/1000 : ℝ)*A^2+(256/1000)*B^2+(277/1000)*C^2+(282/1000)*D^2+
      (284/1000)*A*B+(284/1000)*A*C+(288/1000)*A*D+
      (286/1000)*B*C+(296/1000)*B*D+(362/1000)*C*D+1) :
    (59/20 : ℝ)*A*B*C < D := by sorry





end D1Bound5
end
