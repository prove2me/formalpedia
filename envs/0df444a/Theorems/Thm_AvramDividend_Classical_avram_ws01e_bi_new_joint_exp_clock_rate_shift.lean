-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_joint_exp_clock_rate_shift
-- name    : AvramDividend.Classical.avram_ws01e_bi_new_joint_exp_clock_rate_shift
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T00:08:41.659342+00:00
-- url     : https://prove2.me/theorems/fb763eda-dea8-4861-b811-64a48fc0eaf6
-- title:
--   Exact joint path-clock exponential-rate shift for arbitrary nonnegative measurable rewards
-- statement:
--   For any probability P, positive real exponential rate p, nonnegative discount q, and arbitrary jointly measurable nonnegative extended-real path-clock reward A, the genuine product-clock law satisfies (p+q) E_{P×Exp(p)}[exp(-q e) A] = p E_{P×Exp(p+q)}[A]. Holds in ENNReal with no integrability or independence hypotheses on A beyond product measurability.
-- source:
--   Exact source-faithful extraction of the private product_exp_rate_shift_ws01a lemma in existing WS1A discounted-joint-pair source; reuse accepted 846f9b05 clock Tonelli and 61f61f32 scalar Exp rate shift, pinned Measurable.lintegral_prod_left' and lintegral_const_mul. Public interface supports the still-open killed-resolvent original-clock versus Esscher-rate transfer without editing WS1A-owned proof sources.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat04_exponential_clock_killed_reward_tonelli
import Theorems.Thm_AvramDividend_Classical_chat04_exponential_discount_rate_shift_lintegral_ws01a

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set Classical
open scoped ENNReal

theorem AvramDividend.Classical.avram_ws01e_bi_new_joint_exp_clock_rate_shift
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p q : ℝ) (hp : 0 < p) (hq : 0 ≤ q)
    (A : Ω × ℝ → ℝ≥0∞) (hA : Measurable A) :
    ENNReal.ofReal (p + q) *
      (∫⁻ z : Ω × ℝ,
        ENNReal.ofReal (Real.exp (-(q * z.2))) * A z
        ∂(P.prod (ProbabilityTheory.expMeasure p))) =
    ENNReal.ofReal p *
      (∫⁻ z : Ω × ℝ, A z
        ∂(P.prod (ProbabilityTheory.expMeasure (p + q)))) := by sorry
