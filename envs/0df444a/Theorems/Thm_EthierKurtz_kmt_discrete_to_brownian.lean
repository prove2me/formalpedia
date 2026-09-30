-- Prove2me | Theorems.Thm_EthierKurtz_kmt_discrete_to_brownian
-- name    : EthierKurtz.kmt_discrete_to_brownian
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-29T20:26:32.518983+00:00
-- url     : https://prove2.me/theorems/eac1b43d-2792-41f1-86a3-d79e81d358d3
-- title:
--   Extend Gaussian increments to Brownian motion
-- statement:
--   A discrete KMT coupling of an iid law and iid standard Gaussian increments, for a centered unit-variance law, can be extended to a coupling with a continuous standard Brownian motion. The Brownian values at the integers equal the Gaussian partial sums, so the strict exponential error bound is retained.
-- source:
--   Brownian bridge extension step for Ethier and Kurtz, Markov Processes: Characterization and Convergence, Chapter 7, Section 5, Theorem 5.1, p. 356.

import Definitions.Def_EthierKurtz_kmtApproximation
import Definitions.Def_EthierKurtz_kmtDiscreteApproximation

open MeasureTheory ProbabilityTheory

namespace EthierKurtz

/-- Add independent Brownian bridges to a Gaussian increment coupling, retaining its integer-time error bound. -/
theorem kmt_discrete_to_brownian
    (μ : ProbabilityMeasure ℝ)
    (hmean : ∫ x : ℝ, x ∂(μ : Measure ℝ) = 0)
    (hvariance : variance (fun x : ℝ => x) (μ : Measure ℝ) = 1)
    (hdisc : kmtDiscreteApproximation μ) :
    kmtApproximation μ := by sorry

end EthierKurtz
