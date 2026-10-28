-- Prove2me | Theorems.Thm_D1Bound5_threePair_quadratic_norm_le
-- name    : D1Bound5.threePair_quadratic_norm_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:26:50.585005+00:00
-- url     : https://prove2.me/theorems/50eec99a-38ca-450d-a3bd-97d87081d502
-- title:
--   Three Pair quadratic norm le
-- statement:
--   The quadratic remainder in the three-pair four-by-four determinant has the sharp coefficient nine when all three errors have size <= epsilon.
-- source:
--   D1Bound5/ProductFivePrefixDet.lean, lines 7-63, SHA-256 f9937f549ad5792258cef7e7ac08638bae75b2a7351c4bdd51aa581d8bdd481f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
open Matrix

namespace D1Bound5


theorem _root_.D1Bound5.threePair_quadratic_norm_le (a b c : ℂ) (epsilon : ℝ)
    (he : 0 ≤ epsilon)
    (ha : ‖a‖ ≤ epsilon) (hb : ‖b‖ ≤ epsilon) (hc : ‖c‖ ≤ epsilon) :
    ‖a^2 + b^2 + c^2 - 2*(a*b + a*c + b*c)‖ ≤
      9*epsilon^2 := by sorry







end D1Bound5
end
