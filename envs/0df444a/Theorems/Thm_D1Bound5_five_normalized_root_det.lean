-- Prove2me | Theorems.Thm_D1Bound5_five_normalized_root_det
-- name    : D1Bound5.five_normalized_root_det
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:45:33.502206+00:00
-- url     : https://prove2.me/theorems/3ca56540-7bae-4f59-8eaf-0208fca2299c
-- title:
--   Five normalized root det
-- statement:
--   The fully normalized five-entry determinant identity for symmetric square-root matrices. Only the final tuple element must be nonzero. The other tuple entries and every off-diagonal square root may vanish.
-- source:
--   D1Bound5/ProductFiveMatrixBridge.lean, lines 94-122, SHA-256 8ea3704fb4c1308113f0fd79cdba0ca29b02390fb0ce0be51946ee093a9ecedc. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_DeterminantNormalization_Definitions
import Definitions.Def_D1Bound5_ProductFiveMatrixBridge_Definitions
import Definitions.Def_D1Bound5_ProductFiveRankTwo_Definitions

section
open Matrix

namespace D1Bound5














theorem _root_.D1Bound5.five_normalized_root_det
    (t u : Fin 5 → ℂ) (M : Matrix (Fin 5) (Fin 5) ℂ)
    (hu : ∀ i, (u i)^2 = t i)
    (hdiag : ∀ i, M i i = t i)
    (hsym : Mᵀ = M)
    (hd : fiveLastValue t ≠ 0) :
    (∏ i, t i) * M.det =
      (fiveLastValue t)^2 *
        (productFiveSchur
          (fivePrefixError (normalizedRootError t u M))
          (fiveLastError (normalizedRootError t u M))
          (fivePrefixValues t) (fiveLastValue t)).det := by sorry

end D1Bound5
end
