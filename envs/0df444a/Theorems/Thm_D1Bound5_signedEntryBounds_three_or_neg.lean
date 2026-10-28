-- Prove2me | Theorems.Thm_D1Bound5_signedEntryBounds_three_or_neg
-- name    : D1Bound5.signedEntryBounds_three_or_neg
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:48:52.927004+00:00
-- url     : https://prove2.me/theorems/c5ed2857-39c9-4292-be74-886613bcef05
-- title:
--   Signed Entry Bounds three or neg
-- statement:
--   Auxiliary result `signedEntryBounds_three_or_neg` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/MixedRootMatrixSigns.lean, lines 21-42, SHA-256 2e004ca5529f8e5abf67259e26a8270075f09b04d9c8093e81458a83e3680457. Project: https://github.com/tomislav-math/d1-bound5-lean

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





theorem _root_.D1Bound5.signedEntryBounds_three_or_neg {R : Type*} [CommRing R]
    (f : R →+* ℂ) (a b r : R) (u v : ℂ)
    (hu : u^2 = f a) (hv : v^2 = f b)
    (hr : r^2 = a*b+1) (hab : 3 ≤ ‖f a * f b‖) :
    SignedEntryBounds f a b u v r (5/9) (25/486) ∨
      SignedEntryBounds f a b u v (-r) (5/9) (25/486) := by sorry











end D1Bound5
namespace D1Bound5





end D1Bound5
end
