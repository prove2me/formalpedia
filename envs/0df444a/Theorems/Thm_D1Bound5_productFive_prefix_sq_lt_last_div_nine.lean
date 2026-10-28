-- Prove2me | Theorems.Thm_D1Bound5_productFive_prefix_sq_lt_last_div_nine
-- name    : D1Bound5.productFive_prefix_sq_lt_last_div_nine
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:39:23.626715+00:00
-- url     : https://prove2.me/theorems/78c5f0f2-c679-4ad5-b6d5-c9cc7a6b8ec3
-- title:
--   Product Five prefix sq lt last div nine
-- statement:
--   The first four ordered moduli are quadratically small relative to the last one once the product-four growth bound applies.
-- source:
--   D1Bound5/ProductFivePrefixSizeCross.lean, lines 8-38, SHA-256 39ff147d52c592f501114d236d32fbc4150cb62823ddd11060e5fcb20af2215f. Project: https://github.com/tomislav-math/d1-bound5-lean

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
open scoped NumberField

namespace D1Bound5


theorem _root_.D1Bound5.productFive_prefix_sq_lt_last_div_nine
    (a b c s d : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hcs : c ≤ s)
    (hb : 3 ≤ b) (hlarge : 2*b*c*s < d) :
    a^2 + b^2 + c^2 + s^2 < (d/9)^2 := by sorry



end D1Bound5

namespace D1Bound5



end D1Bound5
end
