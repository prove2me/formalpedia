-- Prove2me | Theorems.Thm_EthierKurtz_kmt_discrete_coupling
-- name    : EthierKurtz.kmt_discrete_coupling
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-29T20:26:18.99598+00:00
-- url     : https://prove2.me/theorems/99bcb804-9d60-4d1f-9d61-159d9ff2e644
-- title:
--   KMT coupling with independent Gaussian increments
-- statement:
--   For a centered real probability law with unit variance and a finite exponential moment around zero, there is a coupling of an iid sample from the law and iid standard Gaussian increments. Their partial sums, uniformly through every positive integer n, differ by more than C log n + x with probability strictly below K exp(-lam x), for positive constants C, K, lam and every x > 0.
-- source:
--   Ethier and Kurtz, Markov Processes: Characterization and Convergence, Chapter 7, Section 5, Theorem 5.1, equation (5.1), p. 356; integer-time Gaussian-increment form of the KMT construction.

import Definitions.Def_EthierKurtz_kmtDiscreteApproximation

open MeasureTheory ProbabilityTheory

namespace EthierKurtz

/-- The probabilistic KMT construction, expressed using Gaussian increments at integer times. -/
theorem kmt_discrete_coupling
    (μ : ProbabilityMeasure ℝ)
    (hexp : ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a : ℝ, |a| ≤ a₀ →
      Integrable (fun x : ℝ => Real.exp (a * x)) (μ : Measure ℝ))
    (hmean : ∫ x : ℝ, x ∂(μ : Measure ℝ) = 0)
    (hvariance : variance (fun x : ℝ => x) (μ : Measure ℝ) = 1) :
    kmtDiscreteApproximation μ := by sorry

end EthierKurtz
