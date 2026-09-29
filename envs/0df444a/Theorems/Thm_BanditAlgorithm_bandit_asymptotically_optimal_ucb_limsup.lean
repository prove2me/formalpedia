-- Prove2me | Theorems.Thm_BanditAlgorithm_bandit_asymptotically_optimal_ucb_limsup
-- name    : BanditAlgorithm.bandit_asymptotically_optimal_ucb_limsup
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-19T02:58:02.937614+00:00
-- url     : https://prove2.me/theorems/3a60f074-c518-4881-aa42-ce6f1e614f9d
-- statement:
--   (Asymptotic optimality) For any 1-subgaussian $k$-armed bandit and any instance of Algorithm 6,
--
--   $$\limsup_{n\to\infty} \frac{R_n}{\log n} \le \sum_{i:\Delta_i>0} \frac{2}{\Delta_i}$$
--
--   — matching the Lai–Robbins lower bound (Mission VII) for unit-variance Gaussian rewards. Stated in $[0,\infty]$ via `ENNReal.ofReal` on both sides (mirroring the Mission VII liminf convention) so the limsup needs no boundedness side conditions.
-- source:
--   L&S Theorem 8.1, Eq. (8.2), p.117

import Definitions.Def_banditRegret
import Definitions.Def_asymptoticUcbPolicy


open MeasureTheory ProbabilityTheory Filter

theorem BanditAlgorithm.bandit_asymptotically_optimal_ucb_limsup {k : ℕ}
    {ν : StochasticBandit k} (hν : IsSubgaussianBandit 1 ν)
    {π : BanditPolicy k} (hπ : IsAsymptoticUCBPolicy π) :
    atTop.limsup
        (fun n : ℕ ↦ ENNReal.ofReal (banditRegret ν π n / Real.log n)) ≤
      ∑ i ∈ Finset.univ.filter (fun i ↦ 0 < banditGap ν i),
        ENNReal.ofReal (2 / banditGap ν i) := by
  sorry
