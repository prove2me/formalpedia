-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_ennreal_product_toReal_bound
-- name    : AvramDividend.Classical.avram_p2_b_rate_ennreal_product_toReal_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:32:05.773705+00:00
-- url     : https://prove2.me/theorems/305dbf4b-a140-481c-aef8-f1456fd6da81
-- title:
--   Convert bounded ENNReal weighted products to finite real-valued bounds
-- statement:
--   If a and C are nonnegative real numbers, and ofReal(a) times an extended nonnegative value is bounded by the finite ofReal(C), then a times the toReal of the value is bounded by C. The finite upper bound rules out the top-value monotonicity obstruction. This enables rigorous conversion of ENNReal marked-event bounds to ordinary small-time real rates.

import Mathlib.Data.ENNReal.Real

open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_b_rate_ennreal_product_toReal_bound
    (a C : ℝ) (b : ENNReal) (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hab : ENNReal.ofReal a * b ≤ ENNReal.ofReal C) :
    a * b.toReal ≤ C := by sorry
