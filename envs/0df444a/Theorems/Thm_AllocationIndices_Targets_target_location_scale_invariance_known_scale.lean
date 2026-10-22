-- Prove2me | Theorems.Thm_AllocationIndices_Targets_target_location_scale_invariance_known_scale
-- name    : AllocationIndices.Targets.target_location_scale_invariance_known_scale
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:39:20.903327+00:00
-- url     : https://prove2.me/theorems/17d9297c-4c65-4f36-906a-8423bfe9d596
-- title:
--   Theorem 7.21 — target process, joint location and scale, σ known: M(φ, x̄, n, σ, T) = M(φ, x̄ + c, n, bσ, bT + c) and ν(x̄, n, σ, T) = ν((x̄ − T)/σ, n, 1, 0)
-- statement:
--   Let observations have the distribution $f(\cdot \mid \mu, \sigma)$ with joint location and scale parameters $\mu$ and $\sigma > 0$, $\sigma$ known, and let $\mu$ have a conjugate prior with parameters $\bar x$, $n > 0$ (and $\sigma$) for which $\bar x$ and $\sigma$ are joint location and scale parameters, updated to $(n\bar x + x)/(n+1)$, $n + 1$ when $x$ is sampled. For the target process with target $T$ in the state $(\bar x, n, \sigma)$ let $M(\varphi, \bar x, n, \sigma, T)$ be the minimal expected number of samples to reach the target against a standard target process with known success probability $\varphi \in (0, 1]$ (7.16), and $\nu(\bar x, n, \sigma, T)$ its Gittins index, with discount factor $0 < a < 1$. Then, as printed in the book, for $b > 0$ and $c \in \mathbb R$,
--   $$M(\varphi, \bar x, n, \sigma, T) = M(\varphi, \bar x + c, n, b\sigma, bT + c),$$
--   and
--   $$\nu(\bar x, n, \sigma, T) = \nu\Big(\frac{\bar x - T}{\sigma}, n, 1, 0\Big).$$
--
--   The second identity reduces the index of the normal target process with known variance to a function of the standardized distance $(\bar x - T)/\sigma$ and of $n$.
--
--   **Formalization Note** This is the theorem as printed. The first identity shifts $\bar x$ by $c$ but does not scale it by $b$, while $\sigma$ and $T$ are scaled; finding F5 shows that it fails for $b \ne 1$ (normal observations, $\varphi = 1/2$, $n = 1$, $T = 0$, $\bar x = 3$, $b = 2$: the left side is at most $1.034$, the right side at least $1.144$), so a disproof of this statement is expected; the corrected statement is posed beside it. The model conventions are those of Theorem 7.13 here: a proper conjugate family with parameters $(\bar x, n, \sigma)$, conjugate for $n > 0$, $\sigma > 0$, the prior concentrated on the known scale $\sigma$; the improper uniform $\pi_0(\mu)$ is replaced as in Corollary 7.22. $M$ is undiscounted, in $[0, \infty]$; $\nu$ is the discrete-time index with discount factor $a \in (0, 1)$.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §7.4 p. 194, Theorem 7.21 (and Corollary 7.22)

import Definitions.Def_AllocationIndices_Targets_Model

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace AllocationIndices.Targets

theorem target_location_scale_invariance_known_scale
    (F : SamplingModel (ℝ × ℝ) (ℝ × ℝ × ℝ))
    (hconj : F.IsConjugateOn {p | 0 < p.2.1 ∧ 0 < p.2.2})
    (hlik : HasJointLocationScale F.likelihood) (hprior : PriorHasJointLocationScaleKnown F.prior)
    (hknown : ∀ p : ℝ × ℝ × ℝ, 0 < p.2.1 → 0 < p.2.2 → F.prior p {θ | θ.2 ≠ p.2.2} = 0)
    (hupd : F.update = knownScaleUpdate) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (xb n σ T : ℝ) (hn : 0 < n) (hσ : 0 < σ) :
    (∀ φ b c : ℝ, 0 < φ → φ ≤ 1 → 0 < b →
      targetCost F T φ (xb, n, σ) = targetCost F (b * T + c) φ (xb + c, n, b * σ)) ∧
    gittinsIndex (F.targetChain T) (F.targetReward T) a (Sum.inl (xb, n, σ)) =
      gittinsIndex (F.targetChain 0) (F.targetReward 0) a (Sum.inl ((xb - T) / σ, n, 1)) := by sorry

end AllocationIndices.Targets
