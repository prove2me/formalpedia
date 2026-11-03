-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_discount_factor_ennreal_le_one
-- name    : AvramDividend.Classical.avram_wave7_11_discount_factor_ennreal_le_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:36:12.242713+00:00
-- url     : https://prove2.me/theorems/c4568e0d-69e4-4ae9-9380-5670d471a1da
-- title:
--   ENNReal discounted dividend payout factor is at most one on nonnegative time
-- statement:
--   At every original dividend payment time t in nonnegative real time, for a nonnegative discount rate q, the ENNReal embedding of exp(-q t) is at most one. This is the exact integrand factor used in the original-process finite-horizon Stieltjes dividend payoff, including the atom at time zero where the factor equals one.
-- source:
--   Deterministic discount estimate for canonical AvramDividend.Classical dividendMeasure integrals, using pinned Mathlib Real.exp_le_one_iff and ENNReal.ofReal_le_ofReal.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.ENNReal.Real

open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_11_discount_factor_ennreal_le_one
    (q : ℝ) (hq : 0 ≤ q) (t : ℝ≥0) :
    ENNReal.ofReal (Real.exp (-(q * (t : ℝ)))) ≤ 1 := by sorry
