-- Prove2me | Theorems.Thm_BanditAlgorithm_adversarial_bandit_exp3ix_high_probability_regret
-- name    : BanditAlgorithm.adversarial_bandit_exp3ix_high_probability_regret
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-17T23:28:47.360606+00:00
-- url     : https://prove2.me/theorems/84240a11-8d46-4f17-8291-aa8bb2ce148e
-- statement:
--   (Exp3-IX high-probability bound, $\delta$-independent learning rate) Let $x \in [0,1]^{n\times k}$ (with $k > 1$, $n \ge 1$) and $\delta \in (0,1)$. Suppose Exp3-IX (Algorithm 10) — with biased loss estimator and exponential weights
--
--   $$\hat Y_{ti} = \frac{\mathbb{1}\{A_t=i\}(1-X_t)}{P_{ti} + \gamma}, \qquad P_{ti} \propto \exp(-\eta \hat L_{t-1,i})$$
--
--   — is run with $\eta = \eta_1 = \sqrt{2\log(k+1)/(nk)}$ and $\gamma = \eta/2$. Then the random regret $\hat R_n = \max_i \sum_{t=1}^n x_{ti} - \sum_{t=1}^n X_t$ satisfies (Eq. 12.5)
--
--   $$\mathbb{P}\left(\hat R_n \ge \sqrt{8nk\log(k+1)} + \sqrt{\frac{nk}{2\log(k+1)}}\,\log\frac{1}{\delta} + \log\frac{k+1}{\delta}\right) \le \delta,$$
--
--   stated as a bound on the `adversarialMeasure` of the bad set of histories.
-- source:
--   L&S Theorem 12.1(1), Eq. (12.5), p.167

import Definitions.Def_AdversarialBandit
import Definitions.Def_exp3Policy


open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.adversarial_bandit_exp3ix_high_probability_regret
    {k : ℕ} (hk : 1 < k) (n : ℕ) (hn : 0 < n)
    (x : ℕ → Fin k → ℝ) (hx : ∀ t : ℕ, ∀ i : Fin k, x t i ∈ Set.Icc (0 : ℝ) 1)
    (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (η : ℝ) (hη : η = Real.sqrt (2 * Real.log (k + 1) / (n * k)))
    (π : BanditPolicy k) (hπ : IsExp3IXPolicy η (η / 2) π) :
    adversarialMeasure x π n
      {h : BanditHistory k n |
        Real.sqrt (8 * n * k * Real.log (k + 1)) +
          Real.sqrt (n * k / (2 * Real.log (k + 1))) * Real.log (1 / δ) +
          Real.log ((k + 1) / δ) ≤ adversarialRandomRegret n x h} ≤
      ENNReal.ofReal δ := by
  sorry
