-- Prove2me | Theorems.Thm_AvramDividend_Classical_negative_jump_full_normalized_exp_deficit_tendsto_zero
-- name    : AvramDividend.Classical.negative_jump_full_normalized_exp_deficit_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:15:53.506058+00:00
-- url     : https://prove2.me/theorems/639c8319-ebaa-45e9-987f-d79d0dae9817
-- title:
--   Truncated-negative-first-moment integrability implies vanishing normalised Lévy exponential deficits over the full negative half-line
-- statement:
--   Under integrability of min(1,|y|) against a negative-jump measure, the real integral of (1-exp(theta*y))/theta over all negative jumps tends to zero as theta tends to infinity. The integrand has an integrable majorant min(1,|y|) when theta is at least one, and converges pointwise to zero with a 1/theta upper bound. Apply Mathlib dominated convergence as in the already proved small-jump version. This establishes the asymptotic physical-drift slope of the bounded-variation exponent, crucial to the finite-mesh zero-barrier no-local-monotonicity proof.
-- source:
--   Proved small_negative_jump_deficit_integral_of_integrable proof pattern and negative_exponential_quotient_bounds; Mathlib dominated convergence.

import Theorems.Thm_AvramDividend_Classical_small_negative_jump_deficit_integral_of_integrable
import Theorems.Thm_AvramDividend_Classical_negative_exponential_quotient_bounds

open Filter MeasureTheory Set
open AvramDividend.Classical

theorem AvramDividend.Classical.negative_jump_full_normalized_exp_deficit_tendsto_zero
    (ν : Measure ℝ)
    (hint : IntegrableOn (fun y : ℝ => min 1 |y|) (Iio (0 : ℝ)) ν) :
    Tendsto
      (fun θ : ℝ => ∫ y in Iio (0 : ℝ),
        (1 - Real.exp (θ * y)) / θ ∂ν)
      atTop (nhds (0 : ℝ)) := by sorry
