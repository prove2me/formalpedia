-- Prove2me | Theorems.Thm_D1Bound5_reference_perturbed_det_ne_zero_of_near
-- name    : D1Bound5.reference_perturbed_det_ne_zero_of_near
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:06:23.504395+00:00
-- url     : https://prove2.me/theorems/fddc2c24-026d-4f1f-8a50-c7680aa7dda5
-- title:
--   Reference perturbed det ne zero of near
-- statement:
--   The reference estimate makes the normalised 4-by-4 correction invertible.
-- source:
--   D1Bound5/ReferencePerturbation.lean, lines 37-42, SHA-256 ec86f12a56b6b3edf6e0b06345cfd19c9831619cf6ee0c116777a8c3288467cc. Project: https://github.com/tomislav-math/d1-bound5-lean

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






theorem _root_.D1Bound5.reference_perturbed_det_ne_zero_of_near
    (F : Matrix (Fin 4) (Fin 4) ℂ)
    (hnear : ‖F - halfOffDiagonal‖ < 3 * (128/8649 : ℝ)) :
    F.det ≠ 0 := by sorry





end D1Bound5
end
