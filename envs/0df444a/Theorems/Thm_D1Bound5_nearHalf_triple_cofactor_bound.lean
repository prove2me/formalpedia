-- Prove2me | Theorems.Thm_D1Bound5_nearHalf_triple_cofactor_bound
-- name    : D1Bound5.nearHalf_triple_cofactor_bound
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:36:42.579287+00:00
-- url     : https://prove2.me/theorems/4b97b38b-c630-4251-8709-36bb73b27c45
-- title:
--   Near Half triple cofactor bound
-- statement:
--   Uniform diagonal cofactor error for three entries near one half.
-- source:
--   D1Bound5/AdjugateFourBounds.lean, lines 112-180, SHA-256 e5781cd0cc609ab6e464413c644de534702a0bca3e48c68b9e060b00a6b88c13. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Util.CollectAxioms
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
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5







end D1Bound5


namespace D1Bound5





end D1Bound5

namespace D1Bound5


theorem _root_.D1Bound5.nearHalf_triple_cofactor_bound (x y z : ℂ)
    (hx : ‖x - (1/2 : ℂ)‖ < (128/8649 : ℝ))
    (hy : ‖y - (1/2 : ℂ)‖ < (128/8649 : ℝ))
    (hz : ‖z - (1/2 : ℂ)‖ < (128/8649 : ℝ)) :
    ‖2*x*y*z - (1/4 : ℂ)‖ < (23/1000 : ℝ) := by sorry

end D1Bound5
end
