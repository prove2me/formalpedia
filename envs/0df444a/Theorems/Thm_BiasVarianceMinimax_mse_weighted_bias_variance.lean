-- Prove2me | Theorems.Thm_BiasVarianceMinimax_mse_weighted_bias_variance
-- name    : BiasVarianceMinimax.mse_weighted_bias_variance
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:32:16.472196+00:00
-- url     : https://prove2.me/theorems/000690a3-244e-4aed-8a86-c93cbcdb3dbf
-- title:
--   (31), first line — the bias-variance form of $\mathrm{MSE}_1^{gen}$
-- statement:
--   For $\tilde d>0$, any model in $\Theta$ and any real weights $w_1,\dots,w_n$,
--
--   $$\mathrm{MSE}_1^{gen}(\hat\theta(\cdot),\tilde d,w)=\Big(\Big(\sum_{j=1}^n w_j-1\Big)\theta+\sum_{j=1}^n w_j\,b(\delta_j)\Big)^2+\sum_{j=1}^n w_j^2\,\mathrm{Var}(\hat\theta(\delta_j)).$$
--
--   When $\sum_j w_j=1$ this is the first line of (31). It turns the expectation in the definition into the two sums the whole analysis works with.
--
--   Differences from the source:
--   - generalization: ∑ⱼ wⱼ = 1 and (∑ⱼ wⱼ b(δⱼ))² + ∑ⱼ wⱼ² Var(v(δⱼ)) → any real weights, with the extra term (∑ⱼ wⱼ − 1)θ; reason: gives the page's line at ∑ⱼ wⱼ = 1, and the sum-to-one step needs the general form
--   - encoding: Var(v(δⱼ)) → the variance of the law of one run; reason: v(δ) and θ̂(δ) differ by a constant
--   - encoding: θ̂(δ) a random variable with independent runs → a law per δ > 0, with runs as coordinates under `Measure.pi` over `Fin n`; reason: the mean squared errors depend only on the laws; same class
-- source:
--   Lam, Zhang & Zhang, arXiv:1902.04673v1, (31), p.25

import Mathlib
import Definitions.Def_BiasVarianceMinimax_mseWeighted

open ProbabilityTheory

namespace BiasVarianceMinimax

/-- **The bias-variance form of `MSE₁`.** Lam, Zhang & Zhang, arXiv:1902.04673v1, (31), p.25, first
line.

**Formalization Note.** The page assumes `∑ⱼ wⱼ = 1` at this point. The statement holds for every
real weight vector with the extra term `(∑ⱼ wⱼ - 1) θ`, and gives the page's line at `∑ⱼ wⱼ = 1`.
`Var(v(δⱼ))` is the variance of the law of one run, since `v(δ)` differs from `θ̂(δ)` by a constant. -/
theorem mse_weighted_bias_variance {q₁ q₂ : ℝ} (M : SimulationOutput q₁ q₂) (n₀ : ℕ) (dTilde : ℝ)
    (hdTilde : 0 < dTilde) (n : ℕ) (w : Fin n → ℝ) :
    mseWeighted M n₀ dTilde n w =
      ((∑ j, w j - 1) * M.θ + ∑ j, w j * M.bias (deltaGrid q₁ q₂ n₀ dTilde j)) ^ 2
        + ∑ j, w j ^ 2 * variance id (M.law (deltaGrid q₁ q₂ n₀ dTilde j)) := by sorry

end BiasVarianceMinimax
