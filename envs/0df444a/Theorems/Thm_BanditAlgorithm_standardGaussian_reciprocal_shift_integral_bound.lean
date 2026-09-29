-- Prove2me | Theorems.Thm_BanditAlgorithm_standardGaussian_reciprocal_shift_integral_bound
-- name    : BanditAlgorithm.standardGaussian_reciprocal_shift_integral_bound
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-30T23:27:44.23236+00:00
-- url     : https://prove2.me/theorems/51b620df-1f46-4772-b50c-73377be7edcf
-- title:
--   Standard Gaussian reciprocal shifted-tail integral bound
-- statement:
--   Let $Z\sim\mathcal N(0,1)$. Conditional on $Z=z$, let $Y_z\sim\mathcal N(z,1)$ and put
--
--   $$
--   G_a(z)=\mathbb P\{Y_z>-a\},\qquad a>0.
--   $$
--
--   There is a universal constant $C>0$ such that
--
--   $$
--   \mathbb E\left[\frac{1}{G_a(Z)}-1\right]\le \frac{C}{a^2}.
--   $$
--
--   This is the scale-free analytic core of the optimal-arm estimate: after standardizing a sample mean based on $s$ unit-variance Gaussian rewards, one has $a=\varepsilon\sqrt{s}$.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), Exercise 36.6(a) and its Gaussian-tail hint, printed p. 475 / PDF p. 484. This is exactly the standardized one-rank Gaussian integral in that exercise.

import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory ProbabilityTheory ENNReal

namespace BanditAlgorithm

/-- The standardized Gaussian reciprocal-tail integral in Exercise 36.6(a). -/
theorem standardGaussian_reciprocal_shift_integral_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ a : ℝ, 0 < a →
        (∫⁻ z, ENNReal.ofReal
            (1 / (gaussianReal z 1).real {x | -a < x} - 1)
            ∂gaussianReal 0 1) ≤
          ENNReal.ofReal (C / a ^ 2) := by
  sorry

end BanditAlgorithm
