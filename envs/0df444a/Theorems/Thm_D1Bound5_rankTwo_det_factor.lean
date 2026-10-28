-- Prove2me | Theorems.Thm_D1Bound5_rankTwo_det_factor
-- name    : D1Bound5.rankTwo_det_factor
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:30:54.507028+00:00
-- url     : https://prove2.me/theorems/a3fc2d10-3dae-4032-9674-27d9ad24ad4e
-- title:
--   Rank Two det factor
-- statement:
--   A four-by-four determinant under a rank-two update reduces exactly to a two-by-two determinant; no adjoints or Hermitian hypotheses.
-- source:
--   D1Bound5/ProductFiveRankTwo.lean, lines 7-28, SHA-256 0cec92c96e51a0a3fbd94ad6a62d3e917e83332e75de37d2fd74599e197b4902. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.rankTwo_det_factor
    (F : Matrix (Fin 4) (Fin 4) ℂ)
    (U : Matrix (Fin 4) (Fin 2) ℂ)
    (V : Matrix (Fin 2) (Fin 4) ℂ)
    (hF : F.det ≠ 0) :
    (F + U * V).det =
      F.det * ((1 : Matrix (Fin 2) (Fin 2) ℂ) + V * F⁻¹ * U).det := by sorry























end D1Bound5
end
