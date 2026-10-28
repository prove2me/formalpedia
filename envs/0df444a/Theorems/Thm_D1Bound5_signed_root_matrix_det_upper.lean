-- Prove2me | Theorems.Thm_D1Bound5_signed_root_matrix_det_upper
-- name    : D1Bound5.signed_root_matrix_det_upper
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:32:33.392887+00:00
-- url     : https://prove2.me/theorems/91fbb58b-914f-47d6-b60b-4173b96f9d0f
-- title:
--   Signed root matrix det upper
-- statement:
--   A signed, symmetric integral root matrix has the required determinant bound as soon as all six normalized entries satisfy the scalar estimates.
-- source:
--   D1Bound5/SymmetricFourDetBound.lean, lines 182-214, SHA-256 2a8b9f67b260c4208f344e6df6c355fa9cb7ed11896ad19c480cd1c58d7b2c1c. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_ProductFourNumericalClosure_Definitions
import Definitions.Def_D1Bound5_RootMatrixSigns_Definitions

section
open Matrix

namespace D1Bound5



end D1Bound5

namespace D1Bound5





end D1Bound5

namespace D1Bound5





end D1Bound5

namespace D1Bound5


theorem _root_.D1Bound5.signed_root_matrix_det_upper
    {R : Type*} [CommRing R] (f : R →+* ℂ)
    (a : Fin 4 → R) (u : Fin 4 → ℂ)
    (S : Matrix (Fin 4) (Fin 4) R)
    (hu : ∀ i, (u i)^2 = f (a i))
    (hdiag : ∀ i, S i i = a i)
    (hsymm : ∀ i j, S i j = S j i)
    (hgood : ∀ i j, i ≠ j →
      SignedEntryGood f (a i) (a j) (u i) (u j) (S i j)) :
    ‖(normalizedRootError (fun i => f (a i)) u
      (fun i j => f (S i j))).det‖ < productFourH * productFourS^3 := by sorry



end D1Bound5
end
