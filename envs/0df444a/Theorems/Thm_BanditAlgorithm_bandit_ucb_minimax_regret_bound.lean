-- Prove2me | Theorems.Thm_BanditAlgorithm_bandit_ucb_minimax_regret_bound
-- name    : BanditAlgorithm.bandit_ucb_minimax_regret_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-17T20:12:22.242532+00:00
-- url     : https://prove2.me/theorems/01d902b3-1604-464f-87ad-69031f482808
-- statement:
--   (UCB distribution-free bound) If $\delta = 1/n^2$, the regret of UCB (Algorithm 3) on any environment $\nu \in \mathcal{E}^k_{SG}(1)$ is bounded by
--
--   $$R_n \le 8\sqrt{nk\log n} + 3\sum_{i=1}^k \Delta_i.$$
-- source:
--   L&S Theorem 7.2, p.108

import Definitions.Def_banditRegret
import Definitions.Def_ucbPolicy


open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.bandit_ucb_minimax_regret_bound {k : ℕ} (hk : 0 < k)
    {ν : StochasticBandit k} (hν : IsSubgaussianBandit 1 ν) {n : ℕ} (hn : 0 < n)
    {π : BanditPolicy k} (hπ : IsUCBPolicy (1 / (n : ℝ) ^ 2) π) :
    banditRegret ν π n ≤
      8 * Real.sqrt (n * k * Real.log n) + 3 * ∑ i, banditGap ν i := by
  sorry
