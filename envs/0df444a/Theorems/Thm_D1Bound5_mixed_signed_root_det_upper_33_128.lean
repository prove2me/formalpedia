-- Prove2me | Theorems.Thm_D1Bound5_mixed_signed_root_det_upper_33_128
-- name    : D1Bound5.mixed_signed_root_det_upper_33_128
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:34:27.366987+00:00
-- url     : https://prove2.me/theorems/3640573f-d14c-4360-898e-168d6e270b5a
-- title:
--   Mixed signed root det upper 33 128
-- statement:
--   The sharp determinant estimate holds for the original-ring mixed signed-root matrix, with the same sign choices as all other mixed estimates.
-- source:
--   D1Bound5/ProductFivePrefixSigned.lean, lines 9-53, SHA-256 67927433726cef75fdd9aa0e90ee3efa28390b5ebb1e6e6ed986d66f238c97c6. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.mixed_signed_root_det_upper_33_128
    {R : Type*} [CommRing R] (f : R →+* ℂ)
    (a : Fin 4 → R) (u : Fin 4 → ℂ)
    (S : Matrix (Fin 4) (Fin 4) R)
    (hu : ∀ i, (u i)^2 = f (a i))
    (hdiag : ∀ i, S i i = a i)
    (hsymm : ∀ i j, S i j = S j i)
    (hgood : ∀ i j, i ≠ j →
      MixedSignedEntryGood f a u i j (S i j)) :
    ‖(normalizedRootError (fun i => f (a i)) u
      (fun i j => f (S i j))).det‖ < (33/128 : ℝ) := by sorry



end D1Bound5
end
