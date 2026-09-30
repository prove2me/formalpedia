-- Prove2me | Theorems.Thm_AllocationIndices_location_invariance_of_index
-- name    : AllocationIndices.location_invariance_of_index
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T03:04:47.233812+00:00
-- url     : https://prove2.me/theorems/68aa4cf1-853a-41aa-a1f8-c4b75f11cf6b
-- title:
--   Theorem 7.9 / Corollary 7.10: for a reward process with a location parameter and a conjugate prior with location parameter x̄, r(x̄ + c, n) = r(x̄, n) + c and ν(x̄, n) = x̄ + ν(0, n)
-- statement:
--   **Theorem 7.9 / Corollary 7.10.** If the parameter $\mu$ for the family of distributions for a reward process is a location parameter, the sample mean $\bar X$ is a sufficient statistic, and $\mu$ has a conjugate prior distribution with the parameters $\bar x$ and $n$, where $\bar x$ is a location parameter and $n \ge 0$, and these parameters take the values $(n\bar x + x)/(n + 1)$ and $n + 1$ when $x$ is the next value sampled, then $\pi_n$ may be identified by its parameters $\bar x$ and $n$, and $\nu(\bar x, n) = \bar x + \nu(0, n)$.
--
--   Formally: for a sampling model on $\Theta = \mathbb{R}$ with parameters $(\bar x, n)$, conjugate for $n > 0$, likelihood with location parameter $\mu$ (`HasLocationParameter`), prior family with location parameter $\bar x$ (`PriorHasLocationParameter`), update `meanUpdate`, integrable observations (the mean of $f(\cdot \mid \theta)$ exists, p. 206), $a \in (0, 1)$, and the discounted rewards of the chain integrable from every state (L&S Assumption 35.6): $r(\bar x + c, n) = r(\bar x, n) + c$ for every $c$, and the Gittins index of the reward process in the state $(\bar x, n)$ equals $\bar x + \nu(0, n)$. The book's improper uniform prior is replaced, as in Corollary 7.10, by a proper conjugate family with a location parameter; the identity $R(\lambda + c, \bar x + c, n) = c(1-a)^{-1} + R(\lambda, \bar x, n)$ for the optimal payoff of $\{S, \Lambda\}$ is not restated.
--
--   **Admissible parameters.** Conjugacy is required, and the conclusion stated, for $n > 0$ only (`IsConjugateOn {p | 0 < p.2}`, `0 < n`): a proper prior has $n > 0$, the book's $n = 0$ being the improper prior of the theorem itself. Conjugacy at every $(\bar x, n) \in \mathbb{R}^2$ cannot hold together with a location parameter. At $n = -1$ the update $(n\bar x + x)/(n+1)$ divides by zero (Lean's value is $0$), so every observation leads to the same state $(0, 0)$. Conjugacy would then force the posterior of the prior $(\bar x, -1)$ to be the prior $(0, 0)$ for every $\bar x$, but by the location structure that posterior moves with $\bar x$. Stated with conjugacy over all of $\mathbb{R}^2$, the theorem had no instances.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §7.4 pp. 189-191, Theorem 7.9 with its proof ((7.17)-(7.21)) and Corollary 7.10

import Definitions.Def_AllocationIndices_Sampling

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace AllocationIndices

/-- **Theorem 7.9 / Corollary 7.10** (pp. 189–191). If the parameter `μ` of the distributions of a
reward process is a location parameter, the sample mean is a sufficient statistic, and `μ` has a
conjugate prior distribution with parameters `x̄` and `n`, where `x̄` is a location parameter of
the prior family and the parameters become `(n x̄ + x)/(n + 1)` and `n + 1` when `x` is the next
value sampled, then the state is identified by `(x̄, n)`, `r(x̄ + c, n) = r(x̄, n) + c`, and
`ν(x̄, n) = x̄ + ν(0, n)`. Stated for the Gittins index of the chain of parameters, under the
book's standing assumptions that the observations have a mean and the discounted rewards are
integrable (L&S Assumption 35.6). -/
theorem location_invariance_of_index (F : SamplingModel ℝ (ℝ × ℝ))
    (hconj : F.IsConjugateOn {p | 0 < p.2})
    (hlik : HasLocationParameter F.likelihood) (hprior : PriorHasLocationParameter F.prior)
    (hupd : F.update = meanUpdate) (hmean : ∀ p, Integrable (fun x : ℝ ↦ x) (F.predictive p))
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hint : DiscountedRewardIntegrable F.rewardChain F.rewardOf a) (xb n : ℝ) (hn : 0 < n) :
    (∀ c : ℝ, F.rewardOf (xb + c, n) = F.rewardOf (xb, n) + c) ∧
    gittinsIndex F.rewardChain F.rewardOf a (xb, n) =
      xb + gittinsIndex F.rewardChain F.rewardOf a (0, n) := by sorry

end AllocationIndices
