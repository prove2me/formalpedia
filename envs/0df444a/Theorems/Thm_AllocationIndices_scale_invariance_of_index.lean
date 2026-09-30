-- Prove2me | Theorems.Thm_AllocationIndices_scale_invariance_of_index
-- name    : AllocationIndices.scale_invariance_of_index
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T03:04:04.755987+00:00
-- url     : https://prove2.me/theorems/8ee33f6c-9798-4ba2-8aee-79cbe4a112cb
-- title:
--   Theorem 7.11 / Corollary 7.12: for a reward process with a scale parameter and a conjugate prior with scale parameter x̄, ν(x̄, n) = x̄ ν(1, n)
-- statement:
--   **Theorem 7.11 / Corollary 7.12.** If the parameter $\sigma > 0$ for the family of distributions for a reward process is a scale parameter, the sample mean is a sufficient statistic, and $\sigma$ has a conjugate prior distribution with the parameters $\bar x$ and $n$, where $\bar x$ is a scale parameter and the parameters take the values $(n\bar x + x)/(n+1)$ and $n + 1$ when $x$ is the next value sampled, then $\pi_n$ may be identified by $\bar x$ and $n$ and $\nu(\bar x, n) = \bar x\,\nu(1, n)$.
--
--   Formally: for a sampling model on $\Theta = \mathbb{R}$ with parameters $(\bar x, n)$, conjugate for $n > 0$, likelihood with scale parameter $\sigma$ (`HasScaleParameter`), prior family with scale parameter $\bar x$ (`PriorHasScaleParameter`), update `meanUpdate`, integrable observations, $a \in (0, 1)$, and the discounted rewards of the chain integrable (L&S Assumption 35.6): $r(b\bar x, n) = b\, r(\bar x, n)$ for $b > 0$, and for $\bar x > 0$ the Gittins index of the reward process satisfies $\nu(\bar x, n) = \bar x\, \nu(1, n)$. (The book's first conclusion, $R(b\lambda, b\bar x, n) = bR(\lambda, \bar x, n)$ for the optimal payoff of $\{S, \Lambda\}$, is not restated.)
--
--   **Admissible parameters.** Conjugacy is required, and the conclusion stated, for $n > 0$ only (`IsConjugateOn {p | 0 < p.2}`, `0 < n`): a proper prior has $n > 0$, the book's $n = 0$ being the improper prior of the theorem itself. Conjugacy at every $(\bar x, n) \in \mathbb{R}^2$ cannot hold together with a location parameter. At $n = -1$ the update $(n\bar x + x)/(n+1)$ divides by zero (Lean's value is $0$), so every observation leads to the same state $(0, 0)$. Conjugacy would then force the posterior of the prior $(\bar x, -1)$ to be the prior $(0, 0)$ for every $\bar x$, but by the location structure that posterior moves with $\bar x$. Stated with conjugacy over all of $\mathbb{R}^2$, the theorem had no instances.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §7.4 pp. 191-192, Theorem 7.11 with its proof and Corollary 7.12

import Definitions.Def_AllocationIndices_Sampling

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace AllocationIndices

/-- **Theorem 7.11 / Corollary 7.12** (pp. 191–192). If the parameter `σ > 0` of the distributions
of a reward process is a scale parameter, the sample mean is a sufficient statistic, and `σ` has a
conjugate prior distribution with parameters `x̄` and `n`, where `x̄` is a scale parameter of the
prior family and the parameters become `(n x̄ + x)/(n + 1)` and `n + 1` when `x` is the next
value sampled, then `r(b x̄, n) = b r(x̄, n)` for `b > 0` and `ν(x̄, n) = x̄ ν(1, n)` for `x̄ > 0`. -/
theorem scale_invariance_of_index (F : SamplingModel ℝ (ℝ × ℝ))
    (hconj : F.IsConjugateOn {p | 0 < p.2})
    (hlik : HasScaleParameter F.likelihood) (hprior : PriorHasScaleParameter F.prior)
    (hupd : F.update = meanUpdate) (hmean : ∀ p, Integrable (fun x : ℝ ↦ x) (F.predictive p))
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hint : DiscountedRewardIntegrable F.rewardChain F.rewardOf a) (xb n : ℝ) (hn : 0 < n) (hxb : 0 < xb) :
    (∀ b : ℝ, 0 < b → F.rewardOf (b * xb, n) = b * F.rewardOf (xb, n)) ∧
    gittinsIndex F.rewardChain F.rewardOf a (xb, n) =
      xb * gittinsIndex F.rewardChain F.rewardOf a (1, n) := by sorry

end AllocationIndices
