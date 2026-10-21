-- Prove2me | Theorems.Thm_AllocationIndices_Targets_target_location_scale_invariance
-- name    : AllocationIndices.Targets.target_location_scale_invariance
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:39:28.395983+00:00
-- url     : https://prove2.me/theorems/82b74fb3-6207-4c50-a2e4-1040bde856e9
-- title:
--   Theorem 7.23 — target process, joint location and scale, σ unknown: M(φ, x̄, s, n, T) = M(φ, bx̄ + c, bs, n, bT + c) and ν(x̄, s, n, T) = ν((x̄ − T)/s, 1, n, 0)
-- statement:
--   Let observations have the distribution $f(\cdot \mid \mu, \sigma)$ with joint location and scale parameters $\mu$ and $\sigma > 0$, both unknown, with a conjugate prior on $(\mu, \sigma)$ with parameters $\bar x$, $s > 0$ and $n > 1$, for which $\bar x$ and $s$ are joint location and scale parameters (the prior with parameters $(b\bar x + c, bs, n)$ is the image of that with parameters $(\bar x, s, n)$ under $(\mu, \sigma) \mapsto (b\mu + c, b\sigma)$), and which change by the rules of the sample mean, sample standard deviation and number of observations when a value is sampled. For the target process with target $T$ in the state $(\bar x, s, n)$ let $M(\varphi, \bar x, s, n, T)$ be the minimal expected number of samples to reach the target against a standard target process with known success probability $\varphi \in (0, 1]$ (7.16), and $\nu(\bar x, s, n, T)$ its Gittins index, with discount factor $0 < a < 1$. Then for $b > 0$ and $c \in \mathbb R$,
--   $$M(\varphi, \bar x, s, n, T) = M(\varphi, b\bar x + c, bs, n, bT + c),$$
--   and
--   $$\nu(\bar x, s, n, T) = \nu\Big(\frac{\bar x - T}{s}, 1, n, 0\Big).$$
--
--   This reduces the index of the normal target process with unknown variance to a two-parameter table, in the standardized distance $(\bar x - T)/s$ and in $n$.
--
--   **Formalization Note** The book writes the left-hand side of the second identity as $\nu(\bar x, s, n, \sigma, T)$; the $\sigma$ there is a stray argument (in this model $\sigma$ is unknown and not part of the state; compare $M(\varphi, \bar x, s, n, T)$ in the same theorem) and is dropped. The book's improper prior $\pi_0(\mu, \sigma) \propto \sigma^{-d}$ is replaced, as in Corollary 7.24 (the counterpart of Corollary 7.16), by a proper conjugate family with parameters $(\bar x, s, n)$, conjugate on $s > 0$, $n > 1$, the domain on which the sample-standard-deviation rule is defined and keeps $s > 0$; the location–scale property of the prior family is the image (pushforward) form, the intended reading of (7.25) (finding F4). The joint location–scale identity of the likelihood is required for all real $(\mu, \sigma)$. $M$ is undiscounted, in $[0, \infty]$; $\nu$ is the discrete-time index with discount factor $a \in (0, 1)$.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §7.4 p. 194, Theorem 7.23 (and Corollary 7.24)

import Definitions.Def_AllocationIndices_Targets_Model

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace AllocationIndices.Targets

theorem target_location_scale_invariance (F : SamplingModel (ℝ × ℝ) (ℝ × ℝ × ℝ))
    (hconj : F.IsConjugateOn {p | 0 < p.2.1 ∧ 1 < p.2.2})
    (hlik : HasJointLocationScale F.likelihood) (hprior : PriorHasJointLocationScale F.prior)
    (hupd : F.update = meanSdUpdate) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (xb s n T : ℝ) (hs : 0 < s) (hn : 1 < n) :
    (∀ φ b c : ℝ, 0 < φ → φ ≤ 1 → 0 < b →
      targetCost F T φ (xb, s, n) = targetCost F (b * T + c) φ (b * xb + c, b * s, n)) ∧
    gittinsIndex (F.targetChain T) (F.targetReward T) a (Sum.inl (xb, s, n)) =
      gittinsIndex (F.targetChain 0) (F.targetReward 0) a (Sum.inl ((xb - T) / s, 1, n)) := by sorry

end AllocationIndices.Targets
