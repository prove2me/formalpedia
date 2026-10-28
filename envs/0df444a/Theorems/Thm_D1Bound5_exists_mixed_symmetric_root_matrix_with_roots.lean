-- Prove2me | Theorems.Thm_D1Bound5_exists_mixed_symmetric_root_matrix_with_roots
-- name    : D1Bound5.exists_mixed_symmetric_root_matrix_with_roots
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:16:48.911231+00:00
-- url     : https://prove2.me/theorems/8361c33c-9287-454b-bebc-47010598ce46
-- title:
--   Exists mixed symmetric root matrix with roots
-- statement:
--   Also choose the four complex square roots, preserving the integral symmetric matrix and the exact root-square equations.
-- source:
--   D1Bound5/MixedRootMatrixSigns.lean, lines 200-226, SHA-256 2e004ca5529f8e5abf67259e26a8270075f09b04d9c8093e81458a83e3680457. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_MixedRootMatrixSigns_Definitions

section
namespace D1Bound5

















end D1Bound5
namespace D1Bound5




theorem _root_.D1Bound5.exists_mixed_symmetric_root_matrix_with_roots
    {R : Type*} [CommRing R] (f : R →+* ℂ)
    (a : Fin 4 → R) (M : Matrix (Fin 4) (Fin 4) R)
    (hdiag : ∀ i, M i i = a i)
    (hsymm : ∀ i j, M i j = M j i)
    (hroot : ∀ i j, i ≠ j → (M i j)^2 = a i * a j + 1)
    (hfirst : ∀ i j, i ≠ j → i = 0 ∨ j = 0 →
      3 ≤ ‖f (a i) * f (a j)‖)
    (hlater : ∀ i j, i ≠ j → ¬(i = 0 ∨ j = 0) →
      9 ≤ ‖f (a i) * f (a j)‖) :
    ∃ (u : Fin 4 → ℂ) (S : Matrix (Fin 4) (Fin 4) R),
      (∀ i, (u i)^2 = f (a i)) ∧
      (∀ i, S i i = a i) ∧
      (∀ i j, S i j = S j i) ∧
      (∀ i j, i ≠ j → S i j = M i j ∨ S i j = -M i j) ∧
      (∀ i j, i ≠ j → (S i j)^2 = a i * a j + 1) ∧
      (∀ i j, i ≠ j → MixedSignedEntryGood f a u i j (S i j)) := by sorry

end D1Bound5
end
