-- Prove2me | Theorems.Thm_AllocationIndices_target_location_invariance
-- name    : AllocationIndices.target_location_invariance
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T03:04:22.694983+00:00
-- url     : https://prove2.me/theorems/db0cdd1b-35e7-4759-b75b-c478ada39423
-- title:
--   Theorem 7.17 / Corollary 7.18: for a target process with a location parameter and a conjugate prior with location parameter x̄, ν(x̄, n, T) = ν(x̄ − T, n, 0)
-- statement:
--   **Theorem 7.17 / Corollary 7.18.** If the parameter $\mu$ for the family of distributions for a target process is a location parameter, the sample mean is a sufficient statistic, and $\mu$ has a conjugate prior distribution with parameters $\bar x$ and $n$ as in Corollary 7.10, then $\nu(\bar x, n, T) = \nu(\bar x - T, n, 0)$.
--
--   Formally: for a sampling model on $\Theta = \mathbb{R}$ with parameters $(\bar x, n)$, conjugate for $n > 0$, likelihood with location parameter $\mu$, prior family with location parameter $\bar x$, update `meanUpdate`, and $a \in (0, 1)$: the Gittins index of the target process with target $T$ in the state $(\bar x, n)$ equals the Gittins index of the target process with target $0$ in the state $(\bar x - T, n)$. (The book's first conclusion, $M(\phi, \bar x, n, T) = M(\phi, \bar x + c, n, T + c)$ for the expected number of samples against a standard target process, is not restated.)
--
--   **Admissible parameters.** Conjugacy is required, and the conclusion stated, for $n > 0$ only (`IsConjugateOn {p | 0 < p.2}`, `0 < n`): a proper prior has $n > 0$, the book's $n = 0$ being the improper prior of the theorem itself. Conjugacy at every $(\bar x, n) \in \mathbb{R}^2$ cannot hold together with a location parameter. At $n = -1$ the update $(n\bar x + x)/(n+1)$ divides by zero (Lean's value is $0$), so every observation leads to the same state $(0, 0)$. Conjugacy would then force the posterior of the prior $(\bar x, -1)$ to be the prior $(0, 0)$ for every $\bar x$, but by the location structure that posterior moves with $\bar x$. Stated with conjugacy over all of $\mathbb{R}^2$, the theorem had no instances.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §7.4 p. 194, Theorem 7.17 (the counterpart of Theorem 7.9 for target processes) and Corollary 7.18

import Definitions.Def_AllocationIndices_Sampling

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace AllocationIndices

/-- **Theorem 7.17 / Corollary 7.18** (p. 194). If the parameter `μ` of the distributions of a
target process is a location parameter, the sample mean is a sufficient statistic, and `μ` has a
conjugate prior distribution with parameters `x̄` and `n` as in Corollary 7.10, then
`ν(x̄, n, T) = ν(x̄ − T, n, 0)`: the index of the target process with target `T` in the state
`(x̄, n)` equals the index of the target process with target `0` in the state `(x̄ − T, n)`. -/
theorem target_location_invariance (F : SamplingModel ℝ (ℝ × ℝ))
    (hconj : F.IsConjugateOn {p | 0 < p.2})
    (hlik : HasLocationParameter F.likelihood) (hprior : PriorHasLocationParameter F.prior)
    (hupd : F.update = meanUpdate) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (xb n T : ℝ)
    (hn : 0 < n) :
    gittinsIndex (F.targetChain T) (F.targetReward T) a (Sum.inl (xb, n)) =
      gittinsIndex (F.targetChain 0) (F.targetReward 0) a (Sum.inl (xb - T, n)) := by sorry

end AllocationIndices
