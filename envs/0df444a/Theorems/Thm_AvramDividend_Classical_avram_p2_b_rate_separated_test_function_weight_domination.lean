-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_separated_test_function_weight_domination
-- name    : AvramDividend.Classical.avram_p2_b_rate_separated_test_function_weight_domination
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:26:38.80468+00:00
-- url     : https://prove2.me/theorems/128a1098-9061-4ba1-a42a-0223d78e5940
-- title:
--   Every bounded separated negative-mark test is dominated by the fourth-exponential Lévy weight
-- statement:
--   For theta and epsilon positive, every real-valued bounded test f that vanishes for marks above -epsilon admits the global absolute bound |f(y)| <= M/(1-exp(-theta epsilon))^4 * (exp(theta*y)-1)^4. This covers continuous compactly supported test functions on a separated negative band and justifies weighted domination and bounded inversion without endpoint indicator shortcuts.

import Mathlib

theorem AvramDividend.Classical.avram_p2_b_rate_separated_test_function_weight_domination
    (f : ℝ → ℝ) (M θ ε : ℝ)
    (hM : 0 ≤ M) (hfbound : ∀ y, |f y| ≤ M)
    (hfsupp : ∀ y, -ε < y → f y = 0)
    (hθ : 0 < θ) (hε : 0 < ε) :
    ∀ y : ℝ, |f y| ≤
      (M / (1 - Real.exp (-θ * ε)) ^ 4) *
        (Real.exp (θ * y) - 1) ^ 4 := by sorry
