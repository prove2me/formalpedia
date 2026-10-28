-- Prove2me | Theorems.Thm_D1Bound5_productFive_schur_scalar_correction_lt
-- name    : D1Bound5.productFive_schur_scalar_correction_lt
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:39:17.549635+00:00
-- url     : https://prove2.me/theorems/daf8eea6-9991-4f07-8842-ad7245ed7e0a
-- title:
--   Product Five schur scalar correction lt
-- statement:
--   Scalar bound for one entry of the rank-two Schur correction. Only ordinary complex division and triangle inequalities are used.
-- source:
--   D1Bound5/ProductFiveSchurNear.lean, lines 54-107, SHA-256 41fb9ec594163d876190b1b792f704711b1efa26be2083527f01269e758125bf. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
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
open Matrix
open scoped Matrix.Norms.L2Operator

namespace D1Bound5






theorem _root_.D1Bound5.productFive_schur_scalar_correction_lt
    (wi wj vi vj d : ℂ)
    (hd : (54 : ℝ) ≤ ‖d‖)
    (hwi : ‖wi/d‖ < (1/18 : ℝ))
    (hwj : ‖wj/d‖ < (1/18 : ℝ))
    (hvi : ‖vi‖ < (3/4 : ℝ))
    (hvj : ‖vj‖ < (3/4 : ℝ)) :
    ‖(wi*vj + vi*wj)/d + vi*vj/d^2‖ < (9/100 : ℝ) := by sorry





end D1Bound5
end
