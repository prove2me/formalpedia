-- Prove2me | Theorems.Thm_BanditAlgorithm_moss_large_gap_arm_expected_pull_bound
-- name    : BanditAlgorithm.moss_large_gap_arm_expected_pull_bound
-- status  : Disproved
-- author  : @MKPynnic
-- created : 2026-07-21T02:37:55.193447+00:00
-- url     : https://prove2.me/theorems/cb54d05f-967b-4c75-9364-0e90663a94c5
-- title:
--   MOSS large-gap arm expected pull bound
-- statement:
--   Fix an arm $i$ with $\Delta_i>8\sqrt{k/n}$ in a 1-subgaussian bandit and run MOSS for horizon $n\ge k>0$. Then $\Delta_i\,\mathbb E[T_i(n)]\le\Delta_i+15\sqrt{n/k}$. The source defines $\kappa_i$, proves $T_i(n)\le\kappa_i$ from the MOSS index rule, and applies Lemma 8.2 to obtain this displayed armwise bound.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), proof of Theorem 9.1, printed pp. 126-127 / PDF pp. 135-136: definition of kappa_i, T_i(n) <= kappa_i, Lemma 8.2 application, and displayed Delta_i E[kappa_i] <= Delta_i + 15 sqrt(n/k).

import Definitions.Def_banditRegret
import Definitions.Def_mossPolicy

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.moss_large_gap_arm_expected_pull_bound
    {k : ℕ} (hk : 0 < k)
    {ν : BanditAlgorithm.StochasticBandit k}
    (hν : BanditAlgorithm.IsSubgaussianBandit 1 ν)
    {n : ℕ} {π : BanditAlgorithm.BanditPolicy k}
    (hπ : BanditAlgorithm.IsMOSSPolicy n π) (hkn : k ≤ n)
    (i : Fin k)
    (hi : 8 * Real.sqrt ((k : ℝ) / n) < BanditAlgorithm.banditGap ν i) :
    BanditAlgorithm.banditGap ν i *
        MeasureTheory.integral
          (BanditAlgorithm.banditMeasure ν π n)
          (fun h ↦ (BanditAlgorithm.armPullCount i h : ℝ)) ≤
      BanditAlgorithm.banditGap ν i + 15 * Real.sqrt ((n : ℝ) / k) := by
  sorry
