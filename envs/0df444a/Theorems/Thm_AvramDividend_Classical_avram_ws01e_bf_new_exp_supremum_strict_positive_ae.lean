-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_exp_supremum_strict_positive_ae
-- name    : AvramDividend.Classical.avram_ws01e_bf_new_exp_supremum_strict_positive_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T23:01:49.645866+00:00
-- url     : https://prove2.me/theorems/9938c3c1-e52a-4dd7-8239-2b151f64019b
-- title:
--   Exponential supremum pushforward implies strict positivity almost everywhere
-- statement:
--   If a measurable real observable S has the exact pushforward law Exp(lam) with lam>0, then S>0 almost surely. The exponential distribution's CDF at zero is exactly zero, and measure_map_apply pulls back the null lower half-line. This is a source-faithful support lemma for the genuine tilted exponential supremum marginal and the weaker single-test threshold-to-transform route.
-- source:
--   Pinned Mathlib ProbabilityTheory.cdf_expMeasure_eq, ofReal_cdf and isProbabilityMeasure_expMeasure; imported genuine Qp supremum law is a future application, not a premise manufactured here.

import Mathlib
import Mathlib.Probability.Distributions.Exponential
import Definitions.Def_AvramDividend_Classical_Reflection
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bf_new_exp_supremum_strict_positive_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) (S : Ω → ℝ) (lam : ℝ)
    (hlam : 0 < lam) (hS : Measurable S)
    (hLaw : Measure.map S μ = expMeasure lam) :
    ∀ᵐ z ∂μ, 0 < S z := by sorry
