-- Prove2me | Theorems.Thm_D1Bound5_mixed_signed_root_adjugate_upper
-- name    : D1Bound5.mixed_signed_root_adjugate_upper
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:48:54.920185+00:00
-- url     : https://prove2.me/theorems/c261e593-3cdf-4024-8fa8-82262dfb1fbc
-- title:
--   Mixed signed root adjugate upper
-- statement:
--   The mixed adjugate estimate for the same integral signed-root matrix used by the mixed determinant estimate.
-- source:
--   D1Bound5/MixedSignedRootAdjugate.lean, lines 8-53, SHA-256 7f2604a22f1326cd9e13496498753b6e57f9db865d688f0cab3a2d3db16522f6. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Util.CollectAxioms
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
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
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5


theorem _root_.D1Bound5.mixed_signed_root_adjugate_upper
    {R : Type*} [CommRing R] (f : R →+* ℂ)
    (a : Fin 4 → R) (u : Fin 4 → ℂ)
    (S : Matrix (Fin 4) (Fin 4) R)
    (hu : ∀ i, (u i)^2 = f (a i))
    (hdiag : ∀ i, S i i = a i)
    (hsymm : ∀ i j, S i j = S j i)
    (hgood : ∀ i j, i ≠ j →
      MixedSignedEntryGood f a u i j (S i j)) :
    ‖(normalizedRootError (fun i => f (a i)) u
      (fun i j => f (S i j))).adjugate‖ <
      (155/96 : ℝ)*(59/96)^2 := by sorry



end D1Bound5
end
