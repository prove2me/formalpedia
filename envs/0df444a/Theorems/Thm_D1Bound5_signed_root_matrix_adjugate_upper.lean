-- Prove2me | Theorems.Thm_D1Bound5_signed_root_matrix_adjugate_upper
-- name    : D1Bound5.signed_root_matrix_adjugate_upper
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:15:42.838045+00:00
-- url     : https://prove2.me/theorems/10bae8ac-4fd3-4188-99c8-600047bd0fba
-- title:
--   Signed root matrix adjugate upper
-- statement:
--   Transfer the adjugate bound to a simultaneously signed root matrix. All entries and signs still live in the original commutative ring.
-- source:
--   D1Bound5/SignedRootAdjugateBound.lean, lines 9-42, SHA-256 532029917d1e0aa4717eb030adcdb1225b1315c3f920d6c92af4241090d272e5. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Util.CollectAxioms
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
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5


theorem _root_.D1Bound5.signed_root_matrix_adjugate_upper
    {R : Type*} [CommRing R] (f : R →+* ℂ)
    (a : Fin 4 → R) (u : Fin 4 → ℂ)
    (S : Matrix (Fin 4) (Fin 4) R)
    (hu : ∀ i, (u i)^2 = f (a i))
    (hdiag : ∀ i, S i i = a i)
    (hsymm : ∀ i j, S i j = S j i)
    (hgood : ∀ i j, i ≠ j →
      SignedEntryGood f (a i) (a j) (u i) (u j) (S i j)) :
    ‖(normalizedRootError (fun i => f (a i)) u
      (fun i j => f (S i j))).adjugate‖ <
        productFourH * productFourS^2 := by sorry



end D1Bound5
end
