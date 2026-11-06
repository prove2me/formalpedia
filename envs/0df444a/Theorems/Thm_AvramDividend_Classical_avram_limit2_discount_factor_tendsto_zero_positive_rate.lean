-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_discount_factor_tendsto_zero_positive_rate
-- name    : AvramDividend.Classical.avram_limit2_discount_factor_tendsto_zero_positive_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:52:37.701196+00:00
-- url     : https://prove2.me/theorems/656303e0-aa07-4fd4-9e83-e895a38b9ae9
-- title:
--   Positive discount rate gives vanishing original dividend terminal discount factors
-- statement:
--   For a genuine positive real discount rate q, the ENNReal embedding of exp(-q n) converges to zero along natural horizons. This is the deterministic discount component for a valid original-process terminal-vanishing condition, without supposing any bound on the random terminal payoff itself.

import Mathlib.Analysis.Complex.Exponential
open Filter
open scoped ENNReal

theorem AvramDividend.Classical.avram_limit2_discount_factor_tendsto_zero_positive_rate
    (q : ℝ) (hq : 0 < q) :
    Filter.Tendsto
      (fun n : ℕ => ENNReal.ofReal (Real.exp (-(q * (n : ℝ)))))
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by sorry
