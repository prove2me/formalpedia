-- Prove2me | Theorems.Thm_BanditAlgorithm_bandit_subgaussian_maximal_inequality
-- name    : BanditAlgorithm.bandit_subgaussian_maximal_inequality
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-19T02:58:12.018859+00:00
-- url     : https://prove2.me/theorems/bbc6c1eb-47b6-4f66-9ae9-cc586c88edf3
-- statement:
--   (Maximal concentration) Let $X_0, X_1, \dots$ be independent $\sigma$-subgaussian ($\sigma > 0$) random variables and $S_t = \sum_{s<t} X_s$. Then for any $\varepsilon > 0$ and $n \ge 1$,
--
--   $$\mathbb{P}\left(\exists\, t \in [1,n] : S_t \ge \varepsilon\right) \le \exp\!\left(-\frac{\varepsilon^2}{2n\sigma^2}\right)$$
--
--   (via Doob's submartingale inequality applied to $\exp(\lambda S_t)$).
-- source:
--   L&S Theorem 9.2, p.125

import Mathlib.Probability.Moments.SubGaussian


open MeasureTheory ProbabilityTheory Real NNReal

theorem BanditAlgorithm.bandit_subgaussian_maximal_inequality
    {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {σ : ℝ≥0} (hσ : 0 < σ)
    (h_indep : iIndepFun X P)
    (h_subG : ∀ i, HasSubgaussianMGF (X i) (σ ^ 2) P)
    {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    P.real {ω | ∃ t, 0 < t ∧ t ≤ n ∧ ε ≤ ∑ s ∈ Finset.range t, X s ω} ≤
      exp (-ε ^ 2 / (2 * n * (σ : ℝ) ^ 2)) := by
  sorry
