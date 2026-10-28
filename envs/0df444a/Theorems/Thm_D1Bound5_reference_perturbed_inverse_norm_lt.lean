-- Prove2me | Theorems.Thm_D1Bound5_reference_perturbed_inverse_norm_lt
-- name    : D1Bound5.reference_perturbed_inverse_norm_lt
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:34:27.592264+00:00
-- url     : https://prove2.me/theorems/6fd9ea1a-92e4-4bb6-ab17-3d683c6c95bb
-- title:
--   Reference perturbed inverse norm lt
-- statement:
--   A strict one-eighth perturbation admits a uniformly bounded inverse.
-- source:
--   D1Bound5/ReferencePerturbation.lean, lines 44-83, SHA-256 ec86f12a56b6b3edf6e0b06345cfd19c9831619cf6ee0c116777a8c3288467cc. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
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
import Definitions.Def_D1Bound5_RootMatrixOperatorBound_Definitions

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5








theorem _root_.D1Bound5.reference_perturbed_inverse_norm_lt
    (F : Matrix (Fin 4) (Fin 4) ℂ)
    (hnear : ‖F - halfOffDiagonal‖ < (1/8 : ℝ)) :
    ‖F⁻¹‖ < (8/3 : ℝ) := by sorry



end D1Bound5
end
