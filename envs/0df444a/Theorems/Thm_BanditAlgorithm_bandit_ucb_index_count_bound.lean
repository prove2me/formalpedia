-- Prove2me | Theorems.Thm_BanditAlgorithm_bandit_ucb_index_count_bound
-- name    : BanditAlgorithm.bandit_ucb_index_count_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-19T02:57:17.651246+00:00
-- url     : https://prove2.me/theorems/ad529627-75d2-42ac-98e0-9c03f2375df5
-- statement:
--   (Core counting lemma) Let $X_0, X_1, \dots$ be independent 1-subgaussian random variables (Mathlib's `HasSubgaussianMGF` with variance proxy 1) on a probability space, and let $\hat\mu_t = \frac{1}{t}\sum_{s<t} X_s$ be the sample mean of the first $t$ of them. For $\varepsilon > 0$, $a > 0$ and the real-valued sum of indicators
--
--   $$\kappa = \sum_{t=1}^n \mathbb{1}\left\{\hat\mu_t + \sqrt{\frac{2a}{t}} \ge \varepsilon\right\},$$
--
--   the expectation satisfies
--
--   $$\mathbb{E}[\kappa] \le 1 + \frac{2}{\varepsilon^2}\left(a + \sqrt{\pi a} + 1\right).$$
-- source:
--   L&S Lemma 8.2, p.118

import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic


open MeasureTheory ProbabilityTheory Real

theorem BanditAlgorithm.bandit_ucb_index_count_bound
    {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ}
    (h_indep : iIndepFun X P)
    (h_subG : ∀ i, HasSubgaussianMGF (X i) 1 P)
    {n : ℕ} {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a) :
    ∫ ω, (∑ t ∈ Finset.Icc 1 n,
        if ε ≤ (∑ s ∈ Finset.range t, X s ω) / t + Real.sqrt (2 * a / t)
          then (1 : ℝ) else 0) ∂P ≤
      1 + 2 / ε ^ 2 * (a + Real.sqrt (Real.pi * a) + 1) := by
  sorry
