-- Prove2me | Theorems.Thm_D1Bound5_mixed_triple_cofactor_radius
-- name    : D1Bound5.mixed_triple_cofactor_radius
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:30:09.119958+00:00
-- url     : https://prove2.me/theorems/8217e70d-ae65-4245-b62f-c4d07b3b7bbb
-- title:
--   Mixed triple cofactor radius
-- statement:
--   A product of three independently perturbed complex half-units.
-- source:
--   D1Bound5/MixedAdjugateScalarBound.lean, lines 8-56, SHA-256 49eb841683fd0e7279ce3834daa64c9419ba6b50d0b8860f85374b8a0264de2d. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.mixed_triple_cofactor_radius (x y z : ℂ) (a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hx : ‖x-(1/2 : ℂ)‖ ≤ a)
    (hy : ‖y-(1/2 : ℂ)‖ ≤ b)
    (hz : ‖z-(1/2 : ℂ)‖ ≤ c) :
    ‖2*x*y*z-(1/4 : ℂ)‖ ≤
      2*a*(1/2+b)*(1/2+c) + b*(1/2+c) + c/2 := by sorry





end D1Bound5


namespace D1Bound5







end D1Bound5
end
