-- Prove2me | Theorems.Thm_D1Bound5_five_normalized_error_symmetric
-- name    : D1Bound5.five_normalized_error_symmetric
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:17:42.923671+00:00
-- url     : https://prove2.me/theorems/56e42a34-6944-4bbe-8576-c50b69ed872e
-- title:
--   Five normalized error symmetric
-- statement:
--   Symmetry survives the square-root normalization, with no nonzero hypotheses on tuple entries or auxiliary roots.
-- source:
--   D1Bound5/ProductFiveExactIdentity.lean, lines 19-32, SHA-256 6ac5997ec73913f4e6c11bdd843ec02784b0283e37205bd8579ba3bcc84fb6a8. Project: https://github.com/tomislav-math/d1-bound5-lean

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

section
open Matrix

namespace D1Bound5




theorem _root_.D1Bound5.five_normalized_error_symmetric
    (t u : Fin 5 → ℂ) (M : Matrix (Fin 5) (Fin 5) ℂ)
    (hsym : Mᵀ = M) :
    (normalizedRootError t u M)ᵀ = normalizedRootError t u M := by sorry



end D1Bound5
end
