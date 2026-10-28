-- Prove2me | Theorems.Thm_D1Bound5_frontier_three_envelope_product
-- name    : D1Bound5.frontier_three_envelope_product
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:28:16.709196+00:00
-- url     : https://prove2.me/theorems/36e3f2f9-dad7-413e-85eb-5d39952e0e94
-- title:
--   Frontier three envelope product
-- statement:
--   Auxiliary result `frontier_three_envelope_product` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FrontierFifteenCofactors.lean, lines 8-42, SHA-256 829c42be3230279544c3ada7eba6c524a34af4542d6dc0b41600e5c49f9ec39c. Project: https://github.com/tomislav-math/d1-bound5-lean

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

theorem _root_.D1Bound5.frontier_three_envelope_product (x y z : ℂ) (a b c : ℝ)
    (ha : 1/2 ≤ a) (hb : 1/2 ≤ b) (hc : 1/2 ≤ c)
    (hx : ‖x-(1/2 : ℂ)‖ ≤ a-1/2)
    (hy : ‖y-(1/2 : ℂ)‖ ≤ b-1/2)
    (hz : ‖z-(1/2 : ℂ)‖ ≤ c-1/2) :
    ‖x*y*z‖ ≤ a*b*c ∧ ‖x*y*z-(1/8 : ℂ)‖ ≤ a*b*c-1/8 := by sorry







end D1Bound5
end
