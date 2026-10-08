-- Prove2me | Theorems.Thm_AvramDividend_Classical_compensated_exponential_min_sq_bound_negative
-- name    : AvramDividend.Classical.compensated_exponential_min_sq_bound_negative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T06:23:35.281906+00:00
-- url     : https://prove2.me/theorems/c88e78d5-33b0-4dc0-a625-dcdd0219b376
-- title:
--   Uniform quadratic-moment domination of the compensated negative exponential kernel
-- statement:
--   For every θ≥0, one coefficient C controls the entire negative-jump Lévy–Khintchine exponential compensation by C*min(1,y²), combining a small-jump Taylor bound and a far-jump exponential bound.
-- source:
--   Lévy–Khintchine compensated kernel and the quadratic Lévy measure condition

import Mathlib

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem compensated_exponential_min_sq_bound_negative (θ : ℝ) (hθ : 0 ≤ θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y < 0,
      ‖Real.exp (θ * y) - 1 -
        θ * (y * (Ioo (-1 : ℝ) 1).indicator
          (fun _ : ℝ => (1 : ℝ)) y)‖ ≤ C * min 1 (y ^ 2) := by sorry

end AvramDividend.Classical
