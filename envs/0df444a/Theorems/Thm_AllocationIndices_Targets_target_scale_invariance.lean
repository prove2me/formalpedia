-- Prove2me | Theorems.Thm_AllocationIndices_Targets_target_scale_invariance
-- name    : AllocationIndices.Targets.target_scale_invariance
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:39:21.983736+00:00
-- url     : https://prove2.me/theorems/5a9d4a24-7a86-414d-b76a-015b626fb859
-- title:
--   Theorem 7.19 — target process with a scale parameter: M(φ, x̄, n, T) = M(φ, bx̄, n, bT) and ν(x̄, n, T) = ν(x̄/T, n, 1)
-- statement:
--   Let observations have the distribution $f(\cdot \mid \sigma)$ with a scale parameter $\sigma > 0$: $f(\cdot \mid b\sigma)$ is the image of $f(\cdot \mid \sigma)$ under $x \mapsto bx$ for $b > 0$. Let $\sigma$ have a conjugate prior with parameters $\bar x$ and $n > 0$, $\bar x$ a scale parameter of the prior family, the parameters becoming $(n\bar x + x)/(n+1)$ and $n + 1$ when $x$ is sampled. Consider the target process with target $T$: it samples until a value $\ge T$ is observed. Let $M(\varphi, \bar x, n, T)$ be the minimal expected number of samples to reach the target (7.16) when this process, in the state $(\bar x, n)$, can be exchanged for good for a standard target process with known success probability $\varphi \in (0, 1]$, and let $\nu(\bar x, n, T)$ be the Gittins index of the target process in the state $(\bar x, n)$, with discount factor $0 < a < 1$. Then for $b > 0$,
--   $$M(\varphi, \bar x, n, T) = M(\varphi, b\bar x, n, bT),$$
--   and, when $T > 0$,
--   $$\nu(\bar x, n, T) = \nu\Big(\frac{\bar x}{T}, n, 1\Big).$$
--
--   Rescaling the observations rescales the state and the target together, so the index of a target process with a scale parameter depends on the state and the target only through their ratio.
--
--   **Formalization Note** The book's improper prior $\pi_0(\sigma) \propto \sigma^{-d}$ is replaced, as in Corollary 7.20 (the counterpart of Corollary 7.12, and as in mission VI), by a proper conjugate family with parameters $(\bar x, n)$, $n > 0$, conjugate for $n > 0$; the published definitions `HasScaleParameter` and `PriorHasScaleParameter` are used. The second identity is stated for $T > 0$: the book does not say so, but $\bar x / T$ is the scale change $b = 1/T$, which must be positive. $M$ is undiscounted and valued in $[0, \infty]$, as in (7.16); $\nu$ is the discrete-time Gittins index (2.6) with discount factor $a \in (0, 1)$ (the identity is the same for every such $a$).
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §7.4 p. 194, Theorem 7.19 (and Corollary 7.20)

import Definitions.Def_AllocationIndices_Targets_Model

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace AllocationIndices.Targets

theorem target_scale_invariance (F : SamplingModel ℝ (ℝ × ℝ))
    (hconj : F.IsConjugateOn {p | 0 < p.2})
    (hlik : HasScaleParameter F.likelihood) (hprior : PriorHasScaleParameter F.prior)
    (hupd : F.update = meanUpdate) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (xb n T : ℝ)
    (hn : 0 < n) :
    (∀ φ b : ℝ, 0 < φ → φ ≤ 1 → 0 < b →
      targetCost F T φ (xb, n) = targetCost F (b * T) φ (b * xb, n)) ∧
    (0 < T →
      gittinsIndex (F.targetChain T) (F.targetReward T) a (Sum.inl (xb, n)) =
        gittinsIndex (F.targetChain 1) (F.targetReward 1) a (Sum.inl (xb / T, n))) := by sorry

end AllocationIndices.Targets
