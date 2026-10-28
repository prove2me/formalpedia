-- Prove2me | Theorems.Thm_D1Bound5_frontier_three_variable_cofactor
-- name    : D1Bound5.frontier_three_variable_cofactor
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:29:34.556567+00:00
-- url     : https://prove2.me/theorems/82820e34-1aca-42d6-a582-7d274b808c6f
-- title:
--   Frontier three variable cofactor
-- statement:
--   Auxiliary result `frontier_three_variable_cofactor` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FrontierFifteenCofactors.lean, lines 44-55, SHA-256 829c42be3230279544c3ada7eba6c524a34af4542d6dc0b41600e5c49f9ec39c. Project: https://github.com/tomislav-math/d1-bound5-lean

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
open Matrix

namespace D1Bound5



theorem _root_.D1Bound5.frontier_three_variable_cofactor (p q r : ℂ) (P Q R : ℝ)
    (hp : ‖p-(1/8 : ℂ)‖ ≤ P-1/8)
    (hq : ‖q-(1/8 : ℂ)‖ ≤ Q-1/8)
    (hr : ‖r-(1/8 : ℂ)‖ ≤ R-1/8) : ‖p-q-r‖ ≤ P+Q+R-1/4 := by sorry





end D1Bound5
end
