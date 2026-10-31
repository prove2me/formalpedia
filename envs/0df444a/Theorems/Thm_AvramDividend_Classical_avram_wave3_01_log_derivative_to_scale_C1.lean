-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_01_log_derivative_to_scale_C1
-- name    : AvramDividend.Classical.avram_wave3_01_log_derivative_to_scale_C1
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T22:31:24.63022+00:00
-- url     : https://prove2.me/theorems/503f29b1-44f0-4387-81cd-260ccc256d1d
-- title:
--   Positive scale function is C¹ from a continuous logarithmic derivative
-- statement:
--   An everywhere positive scale function with a continuous logarithmic derivative has derivative W(x) κ(x), which is continuous, and hence is continuously differentiable on positive reserves.
-- source:
--   Wave3 genuine infinite small jump C1 integration

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_continuous_derivative_to_c1
open AvramDividend.Classical Set Filter

theorem AvramDividend.Classical.avram_wave3_01_log_derivative_to_scale_C1
    (W κ : ℝ → ℝ)
    (hWpos : ∀ a : ℝ, 0 < a → 0 < W a)
    (hκ : ContinuousOn κ (Ioi (0 : ℝ)))
    (hlog : ∀ a : ℝ, 0 < a →
      HasDerivAt (fun x : ℝ => Real.log (W x)) (κ a) a) :
    ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) := by sorry
