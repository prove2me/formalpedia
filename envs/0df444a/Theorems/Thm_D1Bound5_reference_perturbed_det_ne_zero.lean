-- Prove2me | Theorems.Thm_D1Bound5_reference_perturbed_det_ne_zero
-- name    : D1Bound5.reference_perturbed_det_ne_zero
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:13:29.054439+00:00
-- url     : https://prove2.me/theorems/28e17270-24cb-4f57-8d2b-00d34f7ed9e1
-- title:
--   Reference perturbed det ne zero
-- statement:
--   A small normalized correction makes the perturbed matrix nonsingular.
-- source:
--   D1Bound5/ReferencePerturbation.lean, lines 22-35, SHA-256 ec86f12a56b6b3edf6e0b06345cfd19c9831619cf6ee0c116777a8c3288467cc. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_ReferenceMatrixSpectral_Definitions
import Definitions.Def_D1Bound5_RootMatrixOperatorBound_Definitions

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5




theorem _root_.D1Bound5.reference_perturbed_det_ne_zero
    (F : Matrix (Fin 4) (Fin 4) ℂ)
    (hc : ‖halfOffDiagonalInverse * (F - halfOffDiagonal)‖ < 1) :
    F.det ≠ 0 := by sorry







end D1Bound5
end
