-- Prove2me | Theorems.Thm_BanditAlgorithm_bandit_regret_decomposition
-- name    : BanditAlgorithm.bandit_regret_decomposition
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-17T20:11:06.737645+00:00
-- url     : https://prove2.me/theorems/9c4b9d59-c480-4e0c-9619-d7ef8f84d3c2
-- statement:
--   (Regret decomposition) For any policy $\pi$ and $k$-armed bandit $\nu$ with finite means,
--
--   $$R_n = \sum_{i=1}^k \Delta_i\, \mathbb{E}[T_i(n)],$$
--
--   where $T_i(n) = \sum_{t=1}^n \mathbb{1}\{A_t = i\}$ is the number of pulls of arm $i$.
-- source:
--   L&S Lemma 4.5, p.62

import Definitions.Def_banditRegret


open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.bandit_regret_decomposition {k : ℕ} (ν : StochasticBandit k)
    (hInt : ∀ i, Integrable id (ν.P i)) (π : BanditPolicy k) (n : ℕ) :
    banditRegret ν π n =
      ∑ i, banditGap ν i *
        ∫ h, (armPullCount i h : ℝ) ∂(banditMeasure ν π n) := by
  sorry
