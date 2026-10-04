-- Prove2me | Theorems.Thm_AgrawalGoyalTS_TwoArmed_beta_cdf_eq_one_sub_binom_cdf
-- name    : AgrawalGoyalTS.TwoArmed.beta_cdf_eq_one_sub_binom_cdf
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T03:06:51.087854+00:00
-- url     : https://prove2.me/theorems/ef07c99e-5f6c-4847-9f63-09c1dd2bfb90
-- title:
--   Fact 1 — Beta–Binomial duality of cdfs
-- statement:
--   Let $\alpha,\beta$ be positive integers and $y\in[0,1]$. Write $F^{beta}_{\alpha,\beta}$ for the cdf of the $\mathrm{Beta}(\alpha,\beta)$ distribution and $F^B_{n,p}$ for the cdf of $\mathrm{Binomial}(n,p)$. Then
--   $$F^{beta}_{\alpha,\beta}(y)=1-F^B_{\alpha+\beta-1,\,y}(\alpha-1).$$
--
--   This identity converts tail probabilities of the Thompson Sampling posterior samples into binomial tail probabilities, which can then be bounded by Chernoff–Hoeffding inequalities.
--
--   **Formalization Note** The restriction $y\in[0,1]$ is implicit in the paper (the binomial parameter must be a probability; the paper's proof uses $\Pr[U\le y]=y$ for uniforms on $[0,1]$).
-- source:
--   Agrawal and Goyal, Analysis of Thompson Sampling for the Multi-armed Bandit Problem, arXiv:1111.1797v3, p. 12, Fact 1

import Mathlib
import Definitions.Def_AgrawalGoyalTS_TwoArmed_BetaBinomial

namespace AgrawalGoyalTS.TwoArmed

/-- Fact 1 (p. 12): for positive integers `α, β` and `y ∈ [0,1]`,
`F^beta_{α,β}(y) = 1 - F^B_{α+β-1,y}(α - 1)`. -/
theorem beta_cdf_eq_one_sub_binom_cdf (α β : ℕ) (hα : 0 < α) (hβ : 0 < β)
    (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    betaCDF (α : ℝ) (β : ℝ) y = 1 - binomCDF (α + β - 1) y ((α : ℝ) - 1) := by sorry

end AgrawalGoyalTS.TwoArmed
