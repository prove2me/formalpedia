-- Prove2me | Theorems.Thm_D1Bound5_exists_mixed_symmetric_root_matrix
-- name    : D1Bound5.exists_mixed_symmetric_root_matrix
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:39:16.646985+00:00
-- url     : https://prove2.me/theorems/062b5ddf-59ce-4044-b551-d461ea8514cc
-- title:
--   Exists mixed symmetric root matrix
-- statement:
--   A single symmetric integral sign choice gives the mixed first-row and later-row bounds, requiring norm >= 3 on the first row and >= 9 elsewhere. No C >= 4 hypothesis is needed for ordered quadruples.
-- source:
--   D1Bound5/MixedRootMatrixSigns.lean, lines 128-198, SHA-256 2e004ca5529f8e5abf67259e26a8270075f09b04d9c8093e81458a83e3680457. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.exists_mixed_symmetric_root_matrix
    {R : Type*} [CommRing R] (f : R →+* ℂ)
    (a : Fin 4 → R) (u : Fin 4 → ℂ)
    (M : Matrix (Fin 4) (Fin 4) R)
    (hu : ∀ i, (u i)^2 = f (a i))
    (hdiag : ∀ i, M i i = a i)
    (hsymm : ∀ i j, M i j = M j i)
    (hroot : ∀ i j, i ≠ j → (M i j)^2 = a i * a j + 1)
    (hfirst : ∀ i j, i ≠ j → i = 0 ∨ j = 0 →
      3 ≤ ‖f (a i) * f (a j)‖)
    (hlater : ∀ i j, i ≠ j → ¬(i = 0 ∨ j = 0) →
      9 ≤ ‖f (a i) * f (a j)‖) :
    ∃ S : Matrix (Fin 4) (Fin 4) R,
      (∀ i, S i i = a i) ∧
      (∀ i j, S i j = S j i) ∧
      (∀ i j, i ≠ j → S i j = M i j ∨ S i j = -M i j) ∧
      (∀ i j, i ≠ j → (S i j)^2 = a i * a j + 1) ∧
      (∀ i j, i ≠ j → MixedSignedEntryGood f a u i j (S i j)) := by sorry



end D1Bound5
end
