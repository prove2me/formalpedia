-- Prove2me | Theorems.Thm_D1Bound5_five_integrated_det_of_symmetric_error
-- name    : D1Bound5.five_integrated_det_of_symmetric_error
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:23:27.047807+00:00
-- url     : https://prove2.me/theorems/8e660c4e-2a17-4d9e-a07d-ae16a1c19b19
-- title:
--   Five integrated det of symmetric error
-- statement:
--   The determinant of the actual Fin 5 matrix is the scalar-block Schur determinant. The equivalence reindexes both rows and columns simultaneously and therefore introduces no permutation sign.
-- source:
--   D1Bound5/ProductFiveMatrixBridge.lean, lines 74-92, SHA-256 8ea3704fb4c1308113f0fd79cdba0ca29b02390fb0ce0be51946ee093a9ecedc. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_ProductFiveMatrixBridge_Definitions
import Definitions.Def_D1Bound5_ProductFiveRankTwo_Definitions

section
open Matrix

namespace D1Bound5












theorem _root_.D1Bound5.five_integrated_det_of_symmetric_error
    (t : Fin 5 → ℂ) (E : Matrix (Fin 5) (Fin 5) ℂ)
    (hdiag : E (Fin.natAdd 4 (0 : Fin 1)) (Fin.natAdd 4 (0 : Fin 1)) = 0)
    (hsym : Eᵀ = E) (hd : fiveLastValue t ≠ 0) :
    (Matrix.of (fun i j => t i * t j + E i j)).det =
      (fiveLastValue t)^2 *
        (productFiveSchur (fivePrefixError E) (fiveLastError E)
          (fivePrefixValues t) (fiveLastValue t)).det := by sorry



end D1Bound5
end
