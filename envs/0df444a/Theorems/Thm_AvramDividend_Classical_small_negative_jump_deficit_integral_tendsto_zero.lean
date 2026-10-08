-- Prove2me | Theorems.Thm_AvramDividend_Classical_small_negative_jump_deficit_integral_tendsto_zero
-- name    : AvramDividend.Classical.small_negative_jump_deficit_integral_tendsto_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-06T12:32:06.881253+00:00
-- url     : https://prove2.me/theorems/597a9d5e-220b-4020-bc87-e7152d39d770
-- title:
--   Dominated convergence for normalized small-negative-jump Laplace deficits
-- statement:
--   Under integrability of the negative-jump first moment on (-1,0), eventual measurability of the normalized exponential-deficit integrand, and support on nonpositive jumps, the integral of (1-exp(theta*y))/theta over (-1,0) converges to zero as theta goes to infinity. This is the principal dominated-convergence step of the bounded-variation Lévy-exponent proof, with support and measurability requirements explicit.
-- source:
--   Pinned Mathlib theorem tendsto_integral_filter_of_dominated_convergence in Mathlib/MeasureTheory/Integral/DominatedConvergence.lean, and authored scalar children neg_jump_exp_over_theta_bound and neg_jump_exp_deficit_div_tendsto_zero. All other hypotheses are explicit; local Lean remains forbidden.

import Mathlib
open Filter MeasureTheory Set

namespace AvramDividend.Classical

theorem small_negative_jump_deficit_integral_tendsto_zero
    (ν : Measure ℝ)
    (hint : IntegrableOn (fun y : ℝ => -y) (Ioo (-1 : ℝ) 0) ν)
    (hmeas : ∀ᶠ θ : ℝ in atTop,
      AEStronglyMeasurable
        (fun y : ℝ => (1 - Real.exp (θ * y)) / θ)
        (ν.restrict (Ioo (-1 : ℝ) 0)))
    (hsupport : ∀ᵐ y ∂(ν.restrict (Ioo (-1 : ℝ) 0)), y ≤ (0 : ℝ)) :
    Tendsto (fun θ : ℝ => ∫ y in (Ioo (-1 : ℝ) 0), (1 - Real.exp (θ * y)) / θ ∂ν)
      atTop (nhds (0 : ℝ)) := by
  sorry

end AvramDividend.Classical
