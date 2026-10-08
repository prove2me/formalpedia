-- Prove2me | Theorems.Thm_AvramDividend_Classical_exp_compensated_jump_min_sq_bound
-- name    : AvramDividend.Classical.exp_compensated_jump_min_sq_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T23:26:33.987616+00:00
-- url     : https://prove2.me/theorems/27ba3103-5252-470d-b9d4-c69b4d73fc07
-- title:
--   Global Lévy moment domination for the compensated exponential jump kernel
-- statement:
--   For θ≥0, the negative-jump Lévy–Khintchine kernel exp(θy)-1-θy 1_{(-1,1)}(y) is bounded by C min(1,y²) uniformly for y<0, with C=max(1,θ²). For -1<y<0 the compensation is active and the global nonpositive Taylor-remainder theorem bounds the kernel by θ²y². For y≤-1 compensation vanishes and 0≤exp(θy)≤1 bounds its norm by 1 while min(1,y²)=1. This is the precise domination needed to show integrability under the stored Lévy square-moment assumption.
-- source:
--   Levy–Khintchine compensation integrability for negative jumps as required for the Avram Dividend generator calculation.

import Mathlib

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical
theorem exp_compensated_jump_min_sq_bound
    (θ : ℝ) (hθ : 0 ≤ θ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ y < 0,
        ‖Real.exp (θ * y) - 1 -
          θ * y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y‖ ≤
          C * min 1 (y ^ 2) := by sorry
end AvramDividend.Classical
