-- Prove2me | Theorems.Thm_D1Bound5_mixed_signed_root_det_upper
-- name    : D1Bound5.mixed_signed_root_det_upper
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:37:16.474899+00:00
-- url     : https://prove2.me/theorems/82574b7e-eaf0-423f-bbee-33754c0ef8d2
-- title:
--   Mixed signed root det upper
-- statement:
--   Determinant bound for an integral symmetric signed-root matrix in the mixed A >= 1, B >= 3 regime, with explicit signed-entry hypotheses.
-- source:
--   D1Bound5/MixedFourDetBound.lean, lines 170-214, SHA-256 863a07b764253ce476290edc497efddecf3c39545921323e93756d8912d3da78. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_MixedRootMatrixSigns_Definitions

section
open Matrix

namespace D1Bound5







end D1Bound5

namespace D1Bound5



end D1Bound5

namespace D1Bound5


theorem _root_.D1Bound5.mixed_signed_root_det_upper
    {R : Type*} [CommRing R] (f : R →+* ℂ)
    (a : Fin 4 → R) (u : Fin 4 → ℂ)
    (S : Matrix (Fin 4) (Fin 4) R)
    (hu : ∀ i, (u i)^2 = f (a i))
    (hdiag : ∀ i, S i i = a i)
    (hsymm : ∀ i j, S i j = S j i)
    (hgood : ∀ i j, i ≠ j →
      MixedSignedEntryGood f a u i j (S i j)) :
    ‖(normalizedRootError (fun i => f (a i)) u
      (fun i j => f (S i j))).det‖ < (3/10 : ℝ) := by sorry

end D1Bound5
end
