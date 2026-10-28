-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_exponential_density_rate_shift_ws01a
-- name    : AvramDividend.Classical.chat04_exponential_density_rate_shift_ws01a
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T17:43:00.172657+00:00
-- url     : https://prove2.me/theorems/d538aed9-e7b3-4d0d-84de-4a24890c1255
-- title:
--   Exact discounted exponential density rate-shift at Lévy resolvent clocks
-- statement:
--   For real p>0, q≥0 and any observation time t, establish the exact ENNReal density relation (p+q) ExpPDF(p,t) exp(−qt)=p ExpPDF(p+q,t). This handles negative time and serves as a reusable algebraic bridge changing an independent p-exponential observation weighted by q-discount into a (p+q)-exponential observation, with no stochastic harmonicity assumptions.
-- source:
--   Mathlib ProbabilityTheory.exponentialPDF_of_nonneg/of_neg and Real.exp_add, with a remotely elaborated Lean proof.

import Mathlib.Probability.Distributions.Exponential
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open ProbabilityTheory Classical
open scoped ENNReal

theorem AvramDividend.Classical.chat04_exponential_density_rate_shift_ws01a (p q t : ℝ) (hp : 0 < p) (hq : 0 ≤ q) :
    ENNReal.ofReal (p + q) * ProbabilityTheory.exponentialPDF p t *
      ENNReal.ofReal (Real.exp (-(q * t))) =
    ENNReal.ofReal p * ProbabilityTheory.exponentialPDF (p + q) t := by sorry
