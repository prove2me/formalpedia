-- Prove2me | Theorems.Thm_D1Bound5_exists_frontier_symmetric_root_matrix
-- name    : D1Bound5.exists_frontier_symmetric_root_matrix
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:28:13.957378+00:00
-- url     : https://prove2.me/theorems/31afcefa-04d2-45b1-8f7d-d1066979db72
-- title:
--   Exists frontier symmetric root matrix
-- statement:
--   All six frontier signs can be selected in the same original ring, with symmetry and exact root equations retained.
-- source:
--   D1Bound5/FrontierRootBounds.lean, lines 49-99, SHA-256 5ac5fb58a6a02be7185c505b7e8b46ec32cf3d7f63d70d44cb4f347f06e6c218. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FrontierRootBounds_Definitions

section
namespace D1Bound5










theorem _root_.D1Bound5.exists_frontier_symmetric_root_matrix
    {R : Type*} [CommRing R] (f : R →+* ℂ)
    (a : Fin 4 → R) (u : Fin 4 → ℂ) (M : Matrix (Fin 4) (Fin 4) R)
    (hu : ∀ i, (u i)^2 = f (a i))
    (hd : ∀ i, M i i = a i) (hsym : ∀ i j, M i j = M j i)
    (hr : ∀ i j, i ≠ j → (M i j)^2 = a i*a j+1)
    (hlarge : ∀ i j, i ≠ j → 5 ≤ ‖f (a i)*f (a j)‖) :
    ∃ S : Matrix (Fin 4) (Fin 4) R,
      (∀ i, S i i = a i) ∧ (∀ i j, S i j = S j i) ∧
      (∀ i j, i ≠ j → (S i j)^2 = a i*a j+1) ∧
      (∀ i j, i ≠ j → FrontierSignedEntryGood f (a i) (a j) (u i) (u j) (S i j)) := by sorry

end D1Bound5
end
