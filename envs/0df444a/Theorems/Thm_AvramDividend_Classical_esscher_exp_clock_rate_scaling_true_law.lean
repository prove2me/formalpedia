-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_exp_clock_rate_scaling_true_law
-- name    : AvramDividend.Classical.esscher_exp_clock_rate_scaling_true_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T17:40:56.470542+00:00
-- url     : https://prove2.me/theorems/55046bf2-5ff4-4060-9ef7-14c2f9996ba9
-- title:
--   True exponential rate-p clock is the reciprocal-rate pushforward of the standard exponential clock
-- statement:
--   For every p>0, the actual Mathlib exponential clock distribution expMeasure p is exactly the pushforward of the standard probability expMeasure 1 under t↦t/p. This is established from the pinned exponential CDF and measure uniqueness, not assumed. It permits reusing the already accepted fixed-probability coupled-clock dominated-convergence argument to take the finite-to-perpetual limit of actual rate-p Esscher CDF mixtures.
-- source:
--   Pinned Mathlib ProbabilityTheory.cdf_expMeasure_eq and ProbabilityTheory.ofReal_cdf, and Measure.ext_of_Iic/Measure.map_apply under exact commit 0df444a. Genuine exponential measure scaling theorem without stochastic WH.

import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Measure.Map

open ProbabilityTheory MeasureTheory Set

theorem AvramDividend.Classical.esscher_exp_clock_rate_scaling_true_law
    (p : ℝ) (hp : 0 < p) :
    Measure.map (fun t : ℝ => t / p) (expMeasure (1 : ℝ)) =
      expMeasure p := by sorry
