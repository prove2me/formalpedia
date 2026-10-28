-- Prove2me | Theorems.Thm_D1Bound5_mixed_offDiagonal_later
-- name    : D1Bound5.mixed_offDiagonal_later
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:30:09.073219+00:00
-- url     : https://prove2.me/theorems/eeb121bc-eb02-4598-95c6-a49fd6f342c0
-- title:
--   Mixed off Diagonal later
-- statement:
--   Off-diagonal cofactor for distinct positive row/column indices.
-- source:
--   D1Bound5/MixedAdjugateScalarBound.lean, lines 211-231, SHA-256 49eb841683fd0e7279ce3834daa64c9419ba6b50d0b8860f85374b8a0264de2d. Project: https://github.com/tomislav-math/d1-bound5-lean

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






theorem _root_.D1Bound5.mixed_offDiagonal_later (x y z u v w : ℂ)
    (hx : ‖x-(1/2 : ℂ)‖ < (1/18 : ℝ))
    (hy : ‖y-(1/2 : ℂ)‖ < (1/18 : ℝ))
    (hz : ‖z-(1/2 : ℂ)‖ < (1/18 : ℝ))
    (hu : ‖u-(1/2 : ℂ)‖ < (1/64 : ℝ))
    (hv : ‖v-(1/2 : ℂ)‖ < (1/64 : ℝ))
    (hw : ‖w-(1/2 : ℂ)‖ < (1/64 : ℝ)) :
    ‖z^2*u-z*y*v-z*x*w+(1/8 : ℂ)‖ < (47/1000 : ℝ) := by sorry

end D1Bound5
end
