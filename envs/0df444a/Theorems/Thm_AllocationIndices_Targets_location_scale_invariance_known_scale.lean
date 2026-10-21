-- Prove2me | Theorems.Thm_AllocationIndices_Targets_location_scale_invariance_known_scale
-- name    : AllocationIndices.Targets.location_scale_invariance_known_scale
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:39:21.521535+00:00
-- url     : https://prove2.me/theorems/7f910957-d484-420c-8dbe-fea5038c18f7
-- title:
--   Theorem 7.13 — joint location and scale, σ known: R(bλ + c, bx̄ + c, n, bσ) = c(1 − a)⁻¹ + bR(λ, x̄, n, σ) and ν(x̄, n, σ) = x̄ + σν(0, n, 1)
-- statement:
--   Let observations $X_1, X_2, \dots$ have the distribution $f(\cdot \mid \mu, \sigma)$, where $\mu$ and $\sigma > 0$ are joint location and scale parameters: $f(\cdot \mid b\mu + c, b\sigma)$ is the image of $f(\cdot \mid \mu, \sigma)$ under $x \mapsto bx + c$ for $b > 0$, $c \in \mathbb R$. The scale $\sigma$ is known, and $\mu$ has a conjugate prior with parameters $\bar x$, $n > 0$ (and $\sigma$), for which $\bar x$ and $\sigma$ are joint location and scale parameters, and which becomes the prior with parameters $(n\bar x + x)/(n+1)$, $n + 1$ when $x$ is the next value sampled. The reward process in the state $(\bar x, n, \sigma)$ earns the predictive mean of the next observation; rewards are discounted by $a^t$, $0 < a < 1$. Write $R(\lambda, \bar x, n, \sigma)$ for the calibration payoff (7.15) of this reward process against a standard bandit process with parameter $\lambda$, and $\nu(\bar x, n, \sigma)$ for its Gittins index. Then for $b > 0$ and $c \in \mathbb R$,
--   $$R(b\lambda + c,\ b\bar x + c,\ n,\ b\sigma) = c(1 - a)^{-1} + b\,R(\lambda, \bar x, n, \sigma),$$
--   and
--   $$\nu(\bar x, n, \sigma) = \bar x + \sigma\,\nu(0, n, 1).$$
--
--   The index of a normal reward process with known variance is thus determined by a one-parameter table, $\nu(0, n, 1)$ as a function of $n$; this is how the book tabulates it in Chapter 8. Theorem 7.13 is the common generalization of the location result (Theorem 7.9) and the scale result (Theorem 7.11).
--
--   **Formalization Note** The book's improper uniform prior $\pi_0(\mu)$ is used only through the proper posteriors it generates; as in Corollary 7.14 (and in mission VI for Theorems 7.9 and 7.11), the state is the parameters $(\bar x, n, \sigma)$ of a proper conjugate family, $n > 0$, required to be conjugate (the update computes the posterior) for $n > 0$, $\sigma > 0$. The parameter space is $(\mu, \sigma) \in \mathbb R^2$; "$\sigma$ known" means the prior with parameters $(\bar x, n, \sigma)$ puts all its mass on the scale value $\sigma$, which the update never changes. The joint location–scale identity of the likelihood is required for all real $(\mu, \sigma)$ and $b > 0$ (as the published `HasScaleParameter` is); every family defined for $\sigma > 0$ extends to one with this property. The observations are integrable and the discounted rewards have finite expectation from every state (the standing assumptions under which the rewards and $R$ are finite). Discrete time: $R$ uses the discrete-time discount $(1-a)^{-1}$, exactly as printed in (7.15).
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §7.4 p. 192, Theorem 7.13, in the form of Corollary 7.14 (p. 193)

import Definitions.Def_AllocationIndices_Targets_Model

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace AllocationIndices.Targets

theorem location_scale_invariance_known_scale (F : SamplingModel (ℝ × ℝ) (ℝ × ℝ × ℝ))
    (hconj : F.IsConjugateOn {p | 0 < p.2.1 ∧ 0 < p.2.2})
    (hlik : HasJointLocationScale F.likelihood) (hprior : PriorHasJointLocationScaleKnown F.prior)
    (hknown : ∀ p : ℝ × ℝ × ℝ, 0 < p.2.1 → 0 < p.2.2 → F.prior p {θ | θ.2 ≠ p.2.2} = 0)
    (hupd : F.update = knownScaleUpdate) (hmean : ∀ p, Integrable (fun x : ℝ ↦ x) (F.predictive p))
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hint : DiscountedRewardIntegrable F.rewardChain F.rewardOf a)
    (xb n σ : ℝ) (hn : 0 < n) (hσ : 0 < σ) :
    (∀ lam b c : ℝ, 0 < b →
      calibrationPayoff F.rewardChain F.rewardOf a (b * lam + c) (b * xb + c, n, b * σ) =
        c * (1 - a)⁻¹ + b * calibrationPayoff F.rewardChain F.rewardOf a lam (xb, n, σ)) ∧
    gittinsIndex F.rewardChain F.rewardOf a (xb, n, σ) =
      xb + σ * gittinsIndex F.rewardChain F.rewardOf a (0, n, 1) := by sorry

end AllocationIndices.Targets
