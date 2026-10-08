-- Prove2me | Theorems.Thm_AvramDividend_Classical_compensated_exponential_quadratic_of_small_argument
-- name    : AvramDividend.Classical.compensated_exponential_quadratic_of_small_argument
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T06:22:12.422986+00:00
-- url     : https://prove2.me/theorems/f13a5b3c-109d-47e3-b15b-edc75d4e088c
-- title:
--   Quadratic compensated-exponential bound for small jumps
-- statement:
--   For |θy|≤1, the exponential Taylor remainder is at most θ²y² in norm. The Lévy small-jump envelope needs this estimate.
-- source:
--   Analytic support for the compensated Lévy generator Laplace calculation in the Avram Dividend mission.

import Mathlib

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem compensated_exponential_quadratic_of_small_argument (θ y : ℝ) (hsmall : ‖θ * y‖ ≤ 1) :
    ‖Real.exp (θ * y) - 1 - θ * y‖ ≤ θ ^ 2 * y ^ 2 := by sorry

end AvramDividend.Classical
