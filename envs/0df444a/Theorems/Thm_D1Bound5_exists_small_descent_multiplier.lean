-- Prove2me | Theorems.Thm_D1Bound5_exists_small_descent_multiplier
-- name    : D1Bound5.exists_small_descent_multiplier
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:32:28.836845+00:00
-- url     : https://prove2.me/theorems/5da1204c-5d71-44e7-a1f8-4bee960d173f
-- title:
--   Exists small descent multiplier
-- statement:
--   A reciprocal pair of complex multipliers with the indicated trace bound has one multiplier strictly inside the disk of radius one fifth.
-- source:
--   D1Bound5/DescentNorm.lean, lines 7-46, SHA-256 e450f6421d89ae185f5175e96fab77ed2aaba23eeb69a15bfdb754a53e2854b4. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

section
namespace D1Bound5


theorem _root_.D1Bound5.exists_small_descent_multiplier (p r0 : ℂ)
    (hr0 : r0^2 = p+1) (hhyper : 7 ≤ ‖2*p+1‖^2) :
    ∃ eta : ℂ, eta^2 = p ∧ ‖2*p+1-2*r0*eta‖ < (1/5 : ℝ) := by sorry



end D1Bound5
end
