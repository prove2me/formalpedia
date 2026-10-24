-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstRecord_ofReal_geometric_tsum
-- name    : AvramDividend.Classical.firstRecord_ofReal_geometric_tsum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:43:22.732622+00:00
-- url     : https://prove2.me/theorems/49320456-cc5e-4de8-b846-f8211157172e
-- title:
--   Exact closed form for first-record real geometric budgets in ENNReal
-- statement:
--   For nonnegative real record increment ε and discount-survival factor p, the countable extended-nonnegative sum of ε p^(n+1) equals ε p divided by 1-p, with division and subtraction interpreted in ENNReal. The identity also covers the diverging p≥1 case using ENNReal's extended conventions. It converts the geometric first-record budget estimates into a closed form before real scale-ratio finite-difference comparisons.
-- source:
--   Mathlib ENNReal.ofReal_mul, ENNReal.ofReal_pow, ENNReal.tsum_mul_left and ENNReal.tsum_geometric_add_one.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ENNReal.Real

theorem AvramDividend.Classical.firstRecord_ofReal_geometric_tsum
    (ε p : ℝ) (hε : 0 ≤ ε) (hp : 0 ≤ p) :
    (∑' n : ℕ, ENNReal.ofReal (ε * p ^ (n + 1))) =
      ENNReal.ofReal ε * (ENNReal.ofReal p * (1 - ENNReal.ofReal p)⁻¹) := by sorry
