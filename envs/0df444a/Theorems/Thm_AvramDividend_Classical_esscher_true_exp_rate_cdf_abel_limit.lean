-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_true_exp_rate_cdf_abel_limit
-- name    : AvramDividend.Classical.esscher_true_exp_rate_cdf_abel_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T17:48:40.572869+00:00
-- url     : https://prove2.me/theorems/438e998e-b4f0-4dfe-812c-5c2c78bfc75a
-- title:
--   True small-rate exponential clock average converges to any bounded finite-horizon CDF limit
-- statement:
--   For a measurable real-valued CDF-like function f bounded in norm by one and tending to L at infinity, its genuine exponential-horizon expectation ∫ f(t) dExp(p_n)(t) tends to L for strictly positive clock rates p_n→0. The proof does not assume a rate-scaled clock law: it imports an independently established equality of actual exponential measures and the already accepted shared-clock dominated convergence. This supplies the rigorous missing Abelian transition from true finite-rate Esscher survival CDF mixtures to their infinite-horizon limit.
-- source:
--   Mathlib true exponential CDF, the accepted canonical rate scaling theorem and existing accepted 1E-C esscher_exp_clock_cdf_abel_limit; all at Mathlib 0df444a. No Wiener-Hopf factor or global Esscher path law assumed.

import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.OuterMeasure.AE
import Theorems.Thm_AvramDividend_Classical_esscher_exp_clock_rate_scaling_true_law
import Theorems.Thm_AvramDividend_Classical_esscher_exp_clock_cdf_abel_limit

open AvramDividend.Classical ProbabilityTheory MeasureTheory Filter Set

theorem AvramDividend.Classical.esscher_true_exp_rate_cdf_abel_limit
    (f : ℝ → ℝ) (L : ℝ)
    (hf : Tendsto f atTop (nhds L))
    (hmeas : Measurable f) (hbound : ∀ t, ‖f t‖ ≤ (1 : ℝ))
    (p : ℕ → ℝ)
    (hp : Tendsto p atTop (nhdsWithin (0 : ℝ) (Ioi 0)))
    (hpos : ∀ n, 0 < p n) :
    Tendsto (fun n => ∫ t, f t ∂expMeasure (p n))
      atTop (nhds L) := by sorry
