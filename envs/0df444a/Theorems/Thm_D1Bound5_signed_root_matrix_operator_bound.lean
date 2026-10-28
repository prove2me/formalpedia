-- Prove2me | Theorems.Thm_D1Bound5_signed_root_matrix_operator_bound
-- name    : D1Bound5.signed_root_matrix_operator_bound
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:06:22.155992+00:00
-- url     : https://prove2.me/theorems/7a3ecdd3-eb47-4575-b07e-754044b78f59
-- title:
--   Signed root matrix operator bound
-- statement:
--   The six signed entry bounds imply the strict Euclidean operator-norm estimate for the full normalized correction matrix.
-- source:
--   D1Bound5/RootMatrixOperatorBound.lean, lines 12-47, SHA-256 bebb47341f2dbce50938d93401ea24ad5d189f7f69df4fffbfa01c87f611352c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_DeterminantNormalization_Definitions
import Definitions.Def_D1Bound5_RootMatrixOperatorBound_Definitions
import Definitions.Def_D1Bound5_RootMatrixSigns_Definitions

section
open scoped Matrix.Norms.L2Operator

namespace D1Bound5




theorem _root_.D1Bound5.signed_root_matrix_operator_bound
    {R : Type*} [CommRing R] (f : R →+* ℂ)
    (a : Fin 4 → R) (u : Fin 4 → ℂ)
    (S : Matrix (Fin 4) (Fin 4) R)
    (hu : ∀ i, (u i)^2 = f (a i))
    (hdiag : ∀ i, S i i = a i)
    (hgood : ∀ i j, i ≠ j →
      SignedEntryGood f (a i) (a j) (u i) (u j) (S i j)) :
    ‖normalizedRootError (fun i => f (a i)) u
      (fun i j => f (S i j)) - halfOffDiagonal‖ <
      3 * (128/8649 : ℝ) := by sorry



end D1Bound5
end
