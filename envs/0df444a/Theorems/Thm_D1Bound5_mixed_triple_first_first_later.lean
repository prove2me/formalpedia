-- Prove2me | Theorems.Thm_D1Bound5_mixed_triple_first_first_later
-- name    : D1Bound5.mixed_triple_first_first_later
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:33:22.925127+00:00
-- url     : https://prove2.me/theorems/df9f5c0b-5536-4e89-bbbb-92b1a1e83cbe
-- title:
--   Mixed triple first first later
-- statement:
--   Positive-index diagonal cofactor: two large and one small perturbation.
-- source:
--   D1Bound5/MixedAdjugateScalarBound.lean, lines 70-80, SHA-256 49eb841683fd0e7279ce3834daa64c9419ba6b50d0b8860f85374b8a0264de2d. Project: https://github.com/tomislav-math/d1-bound5-lean

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






theorem _root_.D1Bound5.mixed_triple_first_first_later (x y z : ℂ)
    (hx : ‖x-(1/2 : ℂ)‖ < (1/18 : ℝ))
    (hy : ‖y-(1/2 : ℂ)‖ < (1/18 : ℝ))
    (hz : ‖z-(1/2 : ℂ)‖ < (1/64 : ℝ)) :
    ‖2*x*y*z-(1/4 : ℂ)‖ < (7/100 : ℝ) := by sorry

end D1Bound5


namespace D1Bound5







end D1Bound5
end
