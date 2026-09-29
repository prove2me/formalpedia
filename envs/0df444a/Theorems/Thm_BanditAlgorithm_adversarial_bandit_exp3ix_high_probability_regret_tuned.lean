-- Prove2me | Theorems.Thm_BanditAlgorithm_adversarial_bandit_exp3ix_high_probability_regret_tuned
-- name    : BanditAlgorithm.adversarial_bandit_exp3ix_high_probability_regret_tuned
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-17T23:29:08.892155+00:00
-- url     : https://prove2.me/theorems/359c7959-7c15-48f7-9490-71c8f4f66479
-- statement:
--   (Exp3-IX high-probability bound, learning rate tuned to $\delta$) Let $x \in [0,1]^{n\times k}$ (with $k > 1$, $n \ge 1$) and $\delta \in (0,1)$. If Exp3-IX is run with $\eta = \eta_2 = \sqrt{(\log k + \log\frac{k+1}{\delta})/(nk)}$ and $\gamma = \eta/2$, then the random regret satisfies (Eq. 12.6)
--
--   $$\mathbb{P}\left(\hat R_n \ge 2\sqrt{\Big(2\log(k+1) + \log\tfrac{1}{\delta}\Big)\,nk} + \log\frac{k+1}{\delta}\right) \le \delta,$$
--
--   stated as a bound on the `adversarialMeasure` of the bad set of histories.
-- source:
--   L&S Theorem 12.1(2), Eq. (12.6), p.167

import Definitions.Def_AdversarialBandit
import Definitions.Def_exp3Policy


open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.adversarial_bandit_exp3ix_high_probability_regret_tuned
    {k : ℕ} (hk : 1 < k) (n : ℕ) (hn : 0 < n)
    (x : ℕ → Fin k → ℝ) (hx : ∀ t : ℕ, ∀ i : Fin k, x t i ∈ Set.Icc (0 : ℝ) 1)
    (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (η : ℝ)
    (hη : η = Real.sqrt ((Real.log k + Real.log ((k + 1) / δ)) / (n * k)))
    (π : BanditPolicy k) (hπ : IsExp3IXPolicy η (η / 2) π) :
    adversarialMeasure x π n
      {h : BanditHistory k n |
        2 * Real.sqrt ((2 * Real.log (k + 1) + Real.log (1 / δ)) * (n * k)) +
          Real.log ((k + 1) / δ) ≤ adversarialRandomRegret n x h} ≤
      ENNReal.ofReal δ := by
  sorry
