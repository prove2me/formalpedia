-- Prove2me | Theorems.Thm_D1Bound5_five_prefix_det_upper_of_mixed_signed_entries
-- name    : D1Bound5.five_prefix_det_upper_of_mixed_signed_entries
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:17:23.986889+00:00
-- url     : https://prove2.me/theorems/ba7cac32-1715-4111-9fa6-a27b41d2bcc4
-- title:
--   Five prefix det upper of mixed signed entries
-- statement:
--   The exact four-entry determinant estimate inside a full five-entry integral root matrix, conditional only on the signed first-four entries. No condition on the fifth row or column is used here.
-- source:
--   D1Bound5/ProductFivePrefixSigned.lean, lines 55-85, SHA-256 67927433726cef75fdd9aa0e90ee3efa28390b5ebb1e6e6ed986d66f238c97c6. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_ProductFiveMatrixBridge_Definitions

section
open Matrix

namespace D1Bound5




theorem _root_.D1Bound5.five_prefix_det_upper_of_mixed_signed_entries
    {R : Type*} [CommRing R] (f : R →+* ℂ)
    (a : Fin 5 → R) (u : Fin 5 → ℂ)
    (S : Matrix (Fin 5) (Fin 5) R)
    (hu : ∀ i, (u i)^2 = f (a i))
    (hdiag : ∀ i, S i i = a i)
    (hsymm : ∀ i j, S i j = S j i)
    (hgood : ∀ i j : Fin 4, i ≠ j →
      MixedSignedEntryGood f
        (fun k => a (Fin.castAdd 1 k)) (fun k => u (Fin.castAdd 1 k))
        i j (S (Fin.castAdd 1 i) (Fin.castAdd 1 j))) :
    ‖(fivePrefixError (normalizedRootError (fun i => f (a i)) u
      (fun i j => f (S i j)))).det‖ < (33/128 : ℝ) := by sorry

end D1Bound5
end
