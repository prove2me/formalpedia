-- Prove2me | Theorems.Thm_BanditAlgorithm_moss_regret_large_gap_occupation_reduction
-- name    : BanditAlgorithm.moss_regret_large_gap_occupation_reduction
-- status  : Proved
-- author  : @MKPynnic
-- created : 2026-07-21T02:29:04.50695+00:00
-- url     : https://prove2.me/theorems/8217fecb-b421-40bb-bcfc-88d6391dd602
-- title:
--   MOSS regret reduction to large-gap occupations
-- statement:
--   For a 1-subgaussian bandit with $k>0$ arms and horizon $n\ge k$, MOSS regret is at most $24\sqrt{kn}$ plus the gap-weighted expected pull counts of arms with $\Delta_i>8\sqrt{k/n}$. This is the source proof stage combining the displayed regret split, the $8\sqrt{kn}$ term, and the bound $\mathbb E[2n\Delta]\le16\sqrt{kn}$.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), proof of Theorem 9.1, printed p. 126 / PDF p. 135: displayed regret decomposition and large-gap split, followed by E[2 n Delta] <= 16 sqrt(k n).

import Definitions.Def_banditRegret
import Definitions.Def_mossPolicy

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.moss_regret_large_gap_occupation_reduction
    {k : ℕ} (hk : 0 < k)
    {ν : BanditAlgorithm.StochasticBandit k}
    (hν : BanditAlgorithm.IsSubgaussianBandit 1 ν)
    {n : ℕ} {π : BanditAlgorithm.BanditPolicy k}
    (hπ : BanditAlgorithm.IsMOSSPolicy n π) (hkn : k ≤ n) :
    BanditAlgorithm.banditRegret ν π n ≤
      24 * Real.sqrt ((k : ℝ) * n) +
        Finset.sum
          (Finset.univ.filter
            (fun i ↦ 8 * Real.sqrt ((k : ℝ) / n) < BanditAlgorithm.banditGap ν i))
          (fun i ↦ BanditAlgorithm.banditGap ν i *
            MeasureTheory.integral
              (BanditAlgorithm.banditMeasure ν π n)
              (fun h ↦ (BanditAlgorithm.armPullCount i h : ℝ))) := by
  sorry
