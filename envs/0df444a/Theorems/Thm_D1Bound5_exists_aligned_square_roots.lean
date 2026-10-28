-- Prove2me | Theorems.Thm_D1Bound5_exists_aligned_square_roots
-- name    : D1Bound5.exists_aligned_square_roots
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:39:50.455983+00:00
-- url     : https://prove2.me/theorems/9fe06873-c8e8-48d2-b557-dbd2d51d35ac
-- title:
--   Exists aligned square roots
-- statement:
--   Choose auxiliary square roots of b,c aligned with a fixed root of bc+1. This is the first estimate in the C>=4 tail proof.
-- source:
--   D1Bound5/TailAnalytic.lean, lines 20-55, SHA-256 5b2309f4fb74010a3b4a60972a7be2b95652fd687910240dc3beb48298c9b28c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

section
namespace D1Bound5




theorem _root_.D1Bound5.exists_aligned_square_roots (b c r : ℂ)
    (hr : r^2 = b*c+1) (hB : 3 ≤ ‖b‖) (hC : 4 ≤ ‖c‖) :
    ∃ beta gamma : ℂ, beta^2 = b ∧ gamma^2 = c ∧
      (39/20 : ℝ)*‖beta‖*‖gamma‖*‖r-beta*gamma‖ < 1 := by sorry

end D1Bound5
end
