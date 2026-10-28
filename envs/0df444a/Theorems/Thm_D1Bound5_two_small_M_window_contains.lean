-- Prove2me | Theorems.Thm_D1Bound5_two_small_M_window_contains
-- name    : D1Bound5.two_small_M_window_contains
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:06:55.252065+00:00
-- url     : https://prove2.me/theorems/0487cca2-5075-445f-980d-1e99361ee67e
-- title:
--   Two small M window contains
-- statement:
--   The actual M endpoints contain the simple power window throughout the remaining two-small box. These are exact rational comparisons.
-- source:
--   D1Bound5/TwoSmallMWindow.lean, lines 6-39, SHA-256 01923ebf8661b40e7df02a892c03d641336b952c4de01415c43f072023fbf04f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

section
namespace D1Bound5


theorem _root_.D1Bound5.two_small_M_window_contains
    (A B S C : ℝ) (hA : 1 ≤ A) (hB : 0 < B) (hB3 : B < 3)
    (hS : 0 < S) (hS8 : S < (10 : ℝ)^8) (hC : 0 < C) :
    4*((8/9 : ℝ)*608^2)^2*B^6*S^16*C^5/(1-1/4000 : ℝ) ≤ (10 : ℝ)^143*C^5 ∧
      C^11/(10 : ℝ)^87 ≤ A^6*C^11/(4*(3920/81 : ℝ)^2*B^4*S^10*(1+1/4000 : ℝ)) := by sorry



end D1Bound5
end
