-- Prove2me | Theorems.Thm_D1Bound5_mixedSignedEntryGood_or_neg
-- name    : D1Bound5.mixedSignedEntryGood_or_neg
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:51:06.11232+00:00
-- url     : https://prove2.me/theorems/e3b430c3-2e0f-4804-95b5-aa0e07400dbf
-- title:
--   Mixed Signed Entry Good or neg
-- statement:
--   Auxiliary result `mixedSignedEntryGood_or_neg` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/MixedRootMatrixSigns.lean, lines 109-123, SHA-256 2e004ca5529f8e5abf67259e26a8270075f09b04d9c8093e81458a83e3680457. Project: https://github.com/tomislav-math/d1-bound5-lean

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















theorem _root_.D1Bound5.mixedSignedEntryGood_or_neg {R : Type*} [CommRing R]
    (f : R →+* ℂ) (a : Fin 4 → R) (u : Fin 4 → ℂ)
    (i j : Fin 4) (r : R)
    (hu : ∀ k, (u k)^2 = f (a k))
    (hr : r^2 = a i*a j+1)
    (hfirst : i = 0 ∨ j = 0 → 3 ≤ ‖f (a i) * f (a j)‖)
    (hlater : ¬(i = 0 ∨ j = 0) → 9 ≤ ‖f (a i) * f (a j)‖) :
    MixedSignedEntryGood f a u i j r ∨
      MixedSignedEntryGood f a u i j (-r) := by sorry

end D1Bound5
namespace D1Bound5





end D1Bound5
end
