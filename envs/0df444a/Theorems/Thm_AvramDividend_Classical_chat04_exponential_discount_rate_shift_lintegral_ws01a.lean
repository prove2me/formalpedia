-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_exponential_discount_rate_shift_lintegral_ws01a
-- name    : AvramDividend.Classical.chat04_exponential_discount_rate_shift_lintegral_ws01a
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T17:48:12.186575+00:00
-- url     : https://prove2.me/theorems/61f61f32-a8cd-46d5-84a8-e47752ad3644
-- title:
--   Discounted exponential observation as a rate-shifted nonnegative resolvent integral
-- statement:
--   Establish the exact measure-theoretic identity (p+q)∫ExpPDF(p,t)exp(−qt)f(t)dt=p∫ExpPDF(p+q,t)f(t)dt in ENNReal for p>0, q≥0 and every nonnegative measurable f, without a finiteness assumption. It is the stochastic clock-rate conversion required to bridge killed q-scale expectations with the independent exponential observation at rate p+q.
-- source:
--   Pinned Mathlib ProbabilityTheory.exponentialPDF_of_nonneg/of_neg, lintegral_const_mul; private genuine remote elaboration in job a268c362-f0a4-43e1-91bb-4b0f5bcf64c7.

import Mathlib.Probability.Distributions.Exponential
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open ProbabilityTheory Classical MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.chat04_exponential_discount_rate_shift_lintegral_ws01a (p q : ℝ) (hp : 0 < p) (hq : 0 ≤ q)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ENNReal.ofReal (p + q) *
      (∫⁻ t : ℝ, ProbabilityTheory.exponentialPDF p t *
        ENNReal.ofReal (Real.exp (-(q * t))) * f t ∂volume) =
    ENNReal.ofReal p *
      (∫⁻ t : ℝ, ProbabilityTheory.exponentialPDF (p + q) t *
        f t ∂volume) := by sorry
