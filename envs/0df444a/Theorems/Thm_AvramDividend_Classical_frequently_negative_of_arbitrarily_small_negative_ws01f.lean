-- Prove2me | Theorems.Thm_AvramDividend_Classical_frequently_negative_of_arbitrarily_small_negative_ws01f
-- name    : AvramDividend.Classical.frequently_negative_of_arbitrarily_small_negative_ws01f
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T00:00:05.290955+00:00
-- url     : https://prove2.me/theorems/e3424137-34b7-4886-bc0a-68f40f7cfdb1
-- title:
--   Arbitrarily small strictly negative values yield a frequently negative positive-time germ
-- statement:
--   A function on the nonnegative real time axis equal to zero initially and attaining strictly negative values before every positive epsilon is frequently strictly negative along the positive-time filter tending to zero. Formalise by selecting a witness below every reciprocal grid point, squeezing the chosen times to zero and using the exact positive-time nhdsWithin filter.
-- source:
--   Mathlib NNReal reciprocal-grid convergence, squeeze theorem and Filter.frequently definition. Generic topology reduction needed for the actual Lévy endpoint assembly.

import Mathlib

open Filter Topology Set
open scoped NNReal

theorem AvramDividend.Classical.frequently_negative_of_arbitrarily_small_negative_ws01f
    (f : ℝ≥0 → ℝ)
    (hzero : f 0 = 0)
    (hsmall : ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧ f s < 0) :
    ∃ᶠ t in nhdsWithin (0 : ℝ≥0) (Ioi 0), f t < 0 := by sorry
