-- Prove2me | Theorems.Thm_D1Bound5_exists_good_symmetric_root_matrix
-- name    : D1Bound5.exists_good_symmetric_root_matrix
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:13:51.401191+00:00
-- url     : https://prove2.me/theorems/4bacf16d-ddba-4a3b-b578-a907516191aa
-- title:
--   Exists good symmetric root matrix
-- statement:
--   The signs can be chosen for all six unordered off-diagonal positions of a symmetric four-by-four integral root matrix simultaneously. The chosen matrix remains symmetric and its entries remain in the original ring. No nonzero-root or distinct-modulus assumptions are used.
-- source:
--   D1Bound5/RootMatrixSigns.lean, lines 47-115, SHA-256 ebdfe7f3d298bcbeeffe34affc4b69cd64eed73b495d78d2fa97d30c70560fcd. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_RootMatrixSigns_Definitions

section
namespace D1Bound5





end D1Bound5

namespace D1Bound5




theorem _root_.D1Bound5.exists_good_symmetric_root_matrix {R : Type*} [CommRing R]
    (f : R →+* ℂ) (a : Fin 4 → R) (u : Fin 4 → ℂ)
    (M : Matrix (Fin 4) (Fin 4) R)
    (hu : ∀ i, (u i)^2 = f (a i))
    (hdiag : ∀ i, M i i = a i)
    (hsymm : ∀ i j, M i j = M j i)
    (hroot : ∀ i j, i ≠ j → (M i j)^2 = a i * a j + 1)
    (hlarge : ∀ i j, i ≠ j → 9 ≤ ‖f (a i) * f (a j)‖) :
    ∃ S : Matrix (Fin 4) (Fin 4) R,
      (∀ i, S i i = a i) ∧
      (∀ i j, S i j = S j i) ∧
      (∀ i j, i ≠ j → S i j = M i j ∨ S i j = -M i j) ∧
      (∀ i j, i ≠ j → (S i j)^2 = a i * a j + 1) ∧
      (∀ i j, i ≠ j → SignedEntryGood f (a i) (a j) (u i) (u j) (S i j)) := by sorry

end D1Bound5

namespace D1Bound5



end D1Bound5
end
