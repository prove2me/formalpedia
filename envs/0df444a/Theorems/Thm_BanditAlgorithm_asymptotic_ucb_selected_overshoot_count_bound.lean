-- Prove2me | Theorems.Thm_BanditAlgorithm_asymptotic_ucb_selected_overshoot_count_bound
-- name    : BanditAlgorithm.asymptotic_ucb_selected_overshoot_count_bound
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-26T02:11:13.666956+00:00
-- url     : https://prove2.me/theorems/27267c2f-ade1-425e-91dd-840b4f369348
-- title:
--   Selected suboptimal-arm UCB overshoot count
-- statement:
--   Let $\nu$ be a $1$-subgaussian bandit, let $i$ be a suboptimal arm with gap $\Delta_i>0$, and suppose $0<\varepsilon<\Delta_i$. Let $V_n(i,\varepsilon)$ count initialized rounds at which $i$ is selected and its UCB index is at least $\mu^*-\varepsilon$. Then
--   $$
--   \mathbb{E}_{\nu}[V_n(i,\varepsilon)]\le
--   \frac{2}{(\Delta_i-\varepsilon)^2}
--   \left(\log f(n)+\sqrt{\pi\log f(n)}+1\right).
--   $$
--   This is the second expectation estimate after Eq. (8.4), obtained by applying Lemma 8.2 with threshold $\Delta_i-\varepsilon$ and $a=\log f(n)$.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), proof of Theorem 8.1, second expectation estimate after Eq. (8.4), printed p. 120 / PDF p. 129, using Lemma 8.2 printed p. 118.

import Definitions.Def_asymptoticUcbFailureCount
import Theorems.Thm_BanditAlgorithm_bandit_ucb_index_count_bound

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.asymptotic_ucb_selected_overshoot_count_bound
    {k : ℕ} {ν : BanditAlgorithm.StochasticBandit k}
    (hν : BanditAlgorithm.IsSubgaussianBandit 1 ν)
    {π : BanditAlgorithm.BanditPolicy k}
    (n : ℕ) (a i : Fin k) (ε : ℝ)
    (ha : BanditAlgorithm.banditArmMean ν a =
      BanditAlgorithm.banditOptimalMean ν)
    (hgap : 0 < BanditAlgorithm.banditGap ν i)
    (hεpos : 0 < ε)
    (hεlt : ε < BanditAlgorithm.banditGap ν i) :
    MeasureTheory.integral (BanditAlgorithm.banditMeasure ν π n)
        (fun h ↦
          (BanditAlgorithm.asymptoticUcbFailureCount ν a i ε h).2) ≤
      2 / (BanditAlgorithm.banditGap ν i - ε) ^ 2 *
        (Real.log (BanditAlgorithm.asymptoticUcbSchedule n) +
          Real.sqrt
            (Real.pi * Real.log (BanditAlgorithm.asymptoticUcbSchedule n)) +
          1) := by sorry
