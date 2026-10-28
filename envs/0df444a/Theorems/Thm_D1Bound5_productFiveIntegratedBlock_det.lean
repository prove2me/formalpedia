-- Prove2me | Theorems.Thm_D1Bound5_productFiveIntegratedBlock_det
-- name    : D1Bound5.productFiveIntegratedBlock_det
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:41:34.910725+00:00
-- url     : https://prove2.me/theorems/05790067-927f-4f67-82fd-371b5cafcc72
-- title:
--   Product Five Integrated Block det
-- statement:
--   Exact block determinant in equation (integrated-3), without requiring the leading four-by-four matrix to be nonsingular.
-- source:
--   D1Bound5/ProductFiveBlockDet.lean, lines 61-80, SHA-256 10e7a7c95556fd99f1056a1878c1c35778ba742ada21bee32a4eb5948f7ada68. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_ProductFiveBlockDet_Definitions
import Definitions.Def_D1Bound5_ProductFiveRankTwo_Definitions

section
open Matrix

namespace D1Bound5






theorem _root_.D1Bound5.productFiveIntegratedBlock_det
    (F : Matrix (Fin 4) (Fin 4) ℂ)
    (f w : Fin 4 → ℂ) (d : ℂ) (hd : d ≠ 0) :
    (productFiveIntegratedBlock F f w d).det =
      d^2 * (productFiveSchur F f w d).det := by sorry

end D1Bound5
end
