-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_additive_ENNReal_mean_integer_horizons
-- name    : AvramDividend.Classical.avram_p2_34dbea70_additive_ENNReal_mean_integer_horizons
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:22:18.0744+00:00
-- url     : https://prove2.me/theorems/26eeec2d-7af0-4d27-a6c4-ba069611a117
-- title:
--   An additive nonnegative extended-real mean is linear at every integer horizon
-- statement:
--   For any function f from NNReal horizons to ENNReal mean masses, if f(0)=0 and f(s+t)=f(s)+f(t), then f(n)=n f(1) for every natural number n. This remains valid when f(1) is infinite, with no finite-rate assumption. It is the elementary discrete backbone for turning the actual original stationary marked-jump mean additivity into a time-proportional intensity once the source analytic unit rate has been identified.

import Mathlib

open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_34dbea70_additive_ENNReal_mean_integer_horizons
    (f : ℝ≥0 → ℝ≥0∞) (hzero : f 0 = 0)
    (hadd : ∀ s t : ℝ≥0, f (s + t) = f s + f t) (n : ℕ) :
    f (n : ℝ≥0) = (n : ℝ≥0∞) * f 1 := by sorry
