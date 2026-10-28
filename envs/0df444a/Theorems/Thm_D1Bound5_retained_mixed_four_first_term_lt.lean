-- Prove2me | Theorems.Thm_D1Bound5_retained_mixed_four_first_term_lt
-- name    : D1Bound5.retained_mixed_four_first_term_lt
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:36:26.491989+00:00
-- url     : https://prove2.me/theorems/1ea09b62-a864-43e1-b7bd-5ab08235ee7f
-- title:
--   Retained mixed four first term lt
-- statement:
--   With A≥1 and B≥3, the first summand of the actual four-anchor form is below one percent after the retained five-entry growth has been established.
-- source:
--   D1Bound5/RetainedMixedFourScalar.lean, lines 5-45, SHA-256 a4ae2cd4aa93ee653bdc1acf1660c5bb84963f8e3f72e7896314845810407848. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
namespace D1Bound5


theorem _root_.D1Bound5.retained_mixed_four_first_term_lt
    (A B S T C D Z : ℝ) (hA : 1 ≤ A) (hB : 3 ≤ B)
    (hS : 0 < S) (hT : 0 < T) (hZ : 0 < Z)
    (hC : 16*B*S*T < C)
    (hD : A^2*C^5/S^2 < D)
    (hroot : (3999/4000 : ℝ)*C*D < Z^2) :
    13*B*S^2*T^3/Z < (1/100 : ℝ) := by sorry



end D1Bound5
end
