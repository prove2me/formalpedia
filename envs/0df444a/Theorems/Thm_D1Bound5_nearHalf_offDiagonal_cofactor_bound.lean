-- Prove2me | Theorems.Thm_D1Bound5_nearHalf_offDiagonal_cofactor_bound
-- name    : D1Bound5.nearHalf_offDiagonal_cofactor_bound
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:13:19.847659+00:00
-- url     : https://prove2.me/theorems/245b484f-2255-4de8-b3f6-0cc9435bc756
-- title:
--   Near Half off Diagonal cofactor bound
-- statement:
--   A precise off-diagonal cofactor estimate for six complex entries near 1/2.
-- source:
--   D1Bound5/AdjugateOffDiagonal.lean, lines 6-128, SHA-256 8c486c90daafb9dd89af32dc3fe1f2ba55d55fc2b7397544af7a0ac1e04b8b6f. Project: https://github.com/tomislav-math/d1-bound5-lean

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
namespace D1Bound5


theorem _root_.D1Bound5.nearHalf_offDiagonal_cofactor_bound (x y z u v w : ℂ)
    (hx : ‖x - (1/2 : ℂ)‖ < (128/8649 : ℝ))
    (hy : ‖y - (1/2 : ℂ)‖ < (128/8649 : ℝ))
    (hz : ‖z - (1/2 : ℂ)‖ < (128/8649 : ℝ))
    (hu : ‖u - (1/2 : ℂ)‖ < (128/8649 : ℝ))
    (hv : ‖v - (1/2 : ℂ)‖ < (128/8649 : ℝ))
    (hw : ‖w - (1/2 : ℂ)‖ < (128/8649 : ℝ)) :
    ‖w^2*x - w*z*u - w*y*v + (1/8 : ℂ)‖ < (197/10000 : ℝ) := by sorry

end D1Bound5
end
