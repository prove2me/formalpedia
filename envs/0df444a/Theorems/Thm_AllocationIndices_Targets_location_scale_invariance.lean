-- Prove2me | Theorems.Thm_AllocationIndices_Targets_location_scale_invariance
-- name    : AllocationIndices.Targets.location_scale_invariance
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:39:24.281849+00:00
-- url     : https://prove2.me/theorems/e60e355b-dd03-4d52-a71d-9a114a496995
-- title:
--   Theorem 7.15 — joint location and scale, σ unknown: R(bλ + c, bx̄ + c, bs, n) = c(1 − a)⁻¹ + bR(λ, x̄, s, n) and ν(x̄, s, n) = x̄ + sν(0, 1, n)
-- statement:
--   Let observations $X_1, X_2, \dots$ have the distribution $f(\cdot \mid \mu, \sigma)$, where $\mu$ and $\sigma > 0$ are joint location and scale parameters: $f(\cdot \mid b\mu + c, b\sigma)$ is the image of $f(\cdot \mid \mu, \sigma)$ under $x \mapsto bx + c$ for $b > 0$, $c \in \mathbb R$. Both are unknown, with a conjugate prior on $(\mu, \sigma)$ with parameters $\bar x$, $s > 0$ and $n > 1$ such that $\bar x$ and $s$ are joint location and scale parameters of the prior family (the prior with parameters $(b\bar x + c, bs, n)$ is the image of the prior with parameters $(\bar x, s, n)$ under $(\mu, \sigma) \mapsto (b\mu + c, b\sigma)$), and such that the parameters change by the rules of the sample mean, sample standard deviation and number of observations when $x$ is the next value sampled:
--   $$\bar x \mapsto \frac{n\bar x + x}{n+1}, \qquad s \mapsto \sqrt{\frac{(n-1)s^2 + n(x - \bar x)^2/(n+1)}{n}}, \qquad n \mapsto n + 1.$$
--   The reward process in the state $(\bar x, s, n)$ earns the predictive mean of the next observation; rewards are discounted by $a^t$, $0 < a < 1$. Let $R(\lambda, \bar x, s, n) = \sup_\tau \{R_\tau + \lambda(1-a)^{-1}E(a^\tau)\}$ be the calibration payoff (7.15) against a standard bandit process with parameter $\lambda$, and $\nu(\bar x, s, n)$ the Gittins index of the reward process. Then for $b > 0$ and $c \in \mathbb R$,
--   $$R(b\lambda + c,\ b\bar x + c,\ bs,\ n) = c(1 - a)^{-1} + b\,R(\lambda, \bar x, s, n),$$
--   and
--   $$\nu(\bar x, s, n) = \bar x + s\,\nu(0, 1, n).$$
--
--   For the normal reward process with unknown mean and variance, the index is therefore determined by the single function $n \mapsto \nu(0, 1, n)$, which is what makes its tabulation in Chapter 8 feasible. The theorem completes the invariance theory whose location (Theorem 7.9) and scale (Theorem 7.11) halves are its special cases.
--
--   **Formalization Note** The book's improper prior $\pi_0(\mu, \sigma) \propto \sigma^{-d}$ is used only through the proper posteriors it generates; as in Corollary 7.16 (and in mission VI for Theorems 7.9 and 7.11) the state is the parameters $(\bar x, s, n)$ of a proper conjugate family, required to be conjugate (the update computes Mathlib's posterior) for $s > 0$, $n > 1$. Corollary 7.16 allows $n \ge 0$, but the sample-standard-deviation rule divides by $n$ and needs $(n - 1)s^2 > 0$ to keep $s$ positive, so the domain is $n > 1$, $s > 0$ (the sample standard deviation is defined from two observations on), which the update preserves. The prior family's location–scale property is stated as an image of measures; the printed density form (7.25) has the Jacobian $b$ instead of $b^2$ and lacks the shift $+c$ in the conditioning argument (finding F4). The joint location–scale identity of the likelihood is required for all real $(\mu, \sigma)$ (every family defined for $\sigma > 0$ extends to one with this property). The observations are integrable and the discounted rewards have finite expectation from every state. Discrete time: $R$ uses the discrete-time discount $(1-a)^{-1}$ exactly as printed. A statement giving only the index identity, or only the reward identity $r(b\bar x + c, bs, n) = b\,r(\bar x, s, n) + c$, would be weaker than the theorem; both conclusions of the book are stated.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §7.4 p. 193, Theorem 7.15, in the form of Corollary 7.16 (pp. 193–194)

import Definitions.Def_AllocationIndices_Targets_Model

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace AllocationIndices.Targets

theorem location_scale_invariance (F : SamplingModel (ℝ × ℝ) (ℝ × ℝ × ℝ))
    (hconj : F.IsConjugateOn {p | 0 < p.2.1 ∧ 1 < p.2.2})
    (hlik : HasJointLocationScale F.likelihood) (hprior : PriorHasJointLocationScale F.prior)
    (hupd : F.update = meanSdUpdate) (hmean : ∀ p, Integrable (fun x : ℝ ↦ x) (F.predictive p))
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hint : DiscountedRewardIntegrable F.rewardChain F.rewardOf a)
    (xb s n : ℝ) (hs : 0 < s) (hn : 1 < n) :
    (∀ lam b c : ℝ, 0 < b →
      calibrationPayoff F.rewardChain F.rewardOf a (b * lam + c) (b * xb + c, b * s, n) =
        c * (1 - a)⁻¹ + b * calibrationPayoff F.rewardChain F.rewardOf a lam (xb, s, n)) ∧
    gittinsIndex F.rewardChain F.rewardOf a (xb, s, n) =
      xb + s * gittinsIndex F.rewardChain F.rewardOf a (0, 1, n) := by sorry

end AllocationIndices.Targets
