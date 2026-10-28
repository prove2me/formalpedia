-- Prove2me | Theorems.Thm_D1Bound5_rankTwo_det_entries
-- name    : D1Bound5.rankTwo_det_entries
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:45:50.347258+00:00
-- url     : https://prove2.me/theorems/a781997a-185b-431b-a089-1593b00d26d9
-- title:
--   Rank Two det entries
-- statement:
--   The explicit two-by-two determinant, with both off-diagonal products retained. This is valid even for nonsymmetric complex F.
-- source:
--   D1Bound5/ProductFiveRankTwo.lean, lines 30-43, SHA-256 0cec92c96e51a0a3fbd94ad6a62d3e917e83332e75de37d2fd74599e197b4902. Project: https://github.com/tomislav-math/d1-bound5-lean

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




theorem _root_.D1Bound5.rankTwo_det_entries
    (F : Matrix (Fin 4) (Fin 4) ℂ)
    (U : Matrix (Fin 4) (Fin 2) ℂ)
    (V : Matrix (Fin 2) (Fin 4) ℂ)
    (hF : F.det ≠ 0) :
    (F + U * V).det = F.det *
      ((1 + (V * F⁻¹ * U) 0 0) *
        (1 + (V * F⁻¹ * U) 1 1) -
        (V * F⁻¹ * U) 0 1 * (V * F⁻¹ * U) 1 0) := by sorry





















end D1Bound5
end
