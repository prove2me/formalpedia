-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_true_exp_noRecord_CDF_vanishes_at_small_shifted_root
-- name    : AvramDividend.Classical.avram_ws01h_true_exp_noRecord_CDF_vanishes_at_small_shifted_root
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T17:16:42.774139+00:00
-- url     : https://prove2.me/theorems/74283c75-db61-4db0-a93e-7ebb805fd87a
-- title:
--   Genuine Exp(λp) no-upcrossing CDF error tends to zero along every vanishing shifted Esscher root
-- statement:
--   For each genuine real exponential distribution expMeasure(lambda p) with strictly positive root-shift rate lambda p at positive discount p, if lambda p tends to zero as p tends to zero through positive values, then the actual measure mass expMeasure(lambda p)(Iic b) of the no-upper-record error tends to zero for every fixed nonnegative upper barrier b. This identifies the exact source probability CDF with the established analytic 1-exp(-lambda p*b) expression using Mathlib's actual exponential distribution CDF, and applies the already accepted analytic small-root limit. The result is the missing exact-measure-to-analytic-limit bridge for the true original Lévy finite-rate Qp no-record renewal bound; it assumes no exit scale identity.
-- source:
--   Pinned Mathlib ProbabilityTheory.cdf_expMeasure_eq and MeasureTheory.ofReal_cdf, Proved avram_ws01h_exponential_small_rate_cdf_limit UUID 8bb46f89.

import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.CDF
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_exponential_small_rate_cdf_limit

open AvramDividend.Classical ProbabilityTheory MeasureTheory Filter Set
open scoped ENNReal Topology

theorem AvramDividend.Classical.avram_ws01h_true_exp_noRecord_CDF_vanishes_at_small_shifted_root
    (b : ℝ) (hb : 0 ≤ b) (lam : ℝ → ℝ)
    (hlampos : ∀ p : ℝ, 0 < p → 0 < lam p)
    (hlam : Tendsto lam (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 (0 : ℝ))) :
    Tendsto (fun p : ℝ => expMeasure (lam p) (Iic b))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 (0 : ℝ≥0∞)) := by sorry
