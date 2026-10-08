-- Prove2me | Theorems.Thm_AvramDividend_Classical_exp_compensated_near_zero_quadratic
-- name    : AvramDividend.Classical.exp_compensated_near_zero_quadratic
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T23:23:16.483736+00:00
-- url     : https://prove2.me/theorems/21d2d0e6-98d1-4667-bd7c-6c3df9f7dfe4
-- title:
--   Quadratic cancellation of the exponential Lévy compensation near zero
-- statement:
--   For θ≥0, on a sufficiently small negative-jump interval the compensated exponential exp(θy)-1-θy is bounded in norm by θ² y². Choose r=1/(1+θ). Then for -r<y<0 the norm of θy is ≤1, and Mathlib's exp Taylor remainder inequality bounds |exp(θy)-1-θy| by |θy|²=θ² y². This is the small-jump cancellation needed for Lévy-integrability of the compensated Laplace exponent.
-- source:
--   Second-order Taylor remainder for the exponential moment kernel in the Lévy–Khintchine representation, used in Avram–Palmowski–Pistorius Lemma 4.

import Mathlib

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical
theorem exp_compensated_near_zero_quadratic
    (θ : ℝ) (hθ : 0 ≤ θ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
      ∀ y ∈ Ioo (-r) 0,
        ‖Real.exp (θ * y) - 1 - θ * y‖ ≤ θ ^ 2 * y ^ 2 := by sorry
end AvramDividend.Classical
