-- Prove2me | Theorems.Thm_BanditAlgorithm_thompson_sampling_pull_count_bound
-- name    : BanditAlgorithm.thompson_sampling_pull_count_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-30T15:43:58.627061+00:00
-- url     : https://prove2.me/theorems/84f11983-6536-452a-809a-e4ae91be5ae1
-- statement:
--   (Pull-count decomposition, L&S Theorem 36.2, stated for the Gaussian instantiation of Algorithm 24 used in Theorem 36.3.) Assume arm $i_0$ is optimal, let $i \ne i_0$ and let $\varepsilon \in \mathbb{R}$ be arbitrary. Then
--
--   $$\mathbb{E}[T_i(n)] \le 1 + \mathbb{E}\left[\sum_{s=0}^{n-1}\left(\frac{1}{G_{i_0 s}} - 1\right)\right] + \mathbb{E}\left[\sum_{s=0}^{n-1} \mathbb{1}\{G_{is} > 1/n\}\right],$$
--
--   where $G_{is} = 1 - F_{is}(\mu_{i_0} - \varepsilon)$ is the posterior tail probability that arm $i$'s sample exceeds $\mu_{i_0} - \varepsilon$ after $s$ plays ($F_{is}$ = CDF of $\mathcal{N}(\hat\mu_{is}, 1/s)$, $F_{i0} = \delta_\infty$). Both sides are stated in $[0,\infty]$ (lintegrals), so no integrability hypotheses are needed — exactly as in the book, where the right-hand side may be infinite.
-- source:
--   L&S Theorem 36.2, p.463

import Definitions.Def_BanditPolicy
import Definitions.Def_ThompsonSampling


open MeasureTheory ProbabilityTheory ENNReal

theorem BanditAlgorithm.thompson_sampling_pull_count_bound {k : ℕ} [NeZero k]
    (ν : StochasticBandit k) {π : BanditPolicy k} (hπ : IsGaussianTSPolicy π)
    (i₀ : Fin k) (h₀ : banditArmMean ν i₀ = banditOptimalMean ν)
    (i : Fin k) (hi : i ≠ i₀) (ε : ℝ) (n : ℕ) :
    ∫⁻ h, (armPullCount i h : ℝ≥0∞) ∂banditMeasure ν π n ≤
      1 + (∫⁻ h, ∑ s ∈ Finset.range n,
            ENNReal.ofReal (1 / gaussianTSTailProb i₀ s (banditArmMean ν i₀ - ε) h - 1)
            ∂banditMeasure ν π n)
        + ∫⁻ h, ∑ s ∈ Finset.range n,
            (if 1 / (n : ℝ) < gaussianTSTailProb i s (banditArmMean ν i₀ - ε) h
              then (1 : ℝ≥0∞) else 0)
            ∂banditMeasure ν π n := by
  sorry
