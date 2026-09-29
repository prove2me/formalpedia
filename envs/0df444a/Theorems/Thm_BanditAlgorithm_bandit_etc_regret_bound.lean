-- Prove2me | Theorems.Thm_BanditAlgorithm_bandit_etc_regret_bound
-- name    : BanditAlgorithm.bandit_etc_regret_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-17T20:11:33.528279+00:00
-- url     : https://prove2.me/theorems/f4573552-126f-43a3-8f03-4431abfad10f
-- statement:
--   (Explore-Then-Commit) When ETC with exploration parameter $m$ interacts with any 1-subgaussian $k$-armed bandit and $1 \le m \le n/k$, its regret satisfies
--
--   $$R_n \le m\sum_{i=1}^k \Delta_i + (n - mk)\sum_{i=1}^k \Delta_i \exp\!\left(-\frac{m\Delta_i^2}{4}\right).$$
-- source:
--   L&S Theorem 6.1, p.92

import Definitions.Def_banditRegret
import Definitions.Def_etcPolicy


open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.bandit_etc_regret_bound {k : ℕ} (hk : 0 < k) {ν : StochasticBandit k}
    (hν : IsSubgaussianBandit 1 ν) {m n : ℕ} (hm : 1 ≤ m) (hmn : m * k ≤ n)
    {π : BanditPolicy k} (hπ : IsETCPolicy hk m π) :
    banditRegret ν π n ≤
      m * ∑ i, banditGap ν i +
        (n - m * k : ℝ) *
          ∑ i, banditGap ν i * Real.exp (-(m * (banditGap ν i) ^ 2) / 4) := by
  sorry
