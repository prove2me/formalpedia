-- Prove2me | Theorems.Thm_BanditAlgorithm_moss_large_gap_occupation_sum_bound
-- name    : BanditAlgorithm.moss_large_gap_occupation_sum_bound
-- status  : Open
-- author  : @MKPynnic
-- created : 2026-07-21T02:30:14.309695+00:00
-- url     : https://prove2.me/theorems/fcaf0495-946b-47dd-b278-b636a8b300ea
-- title:
--   MOSS large-gap occupation sum bound
-- statement:
--   For a 1-subgaussian bandit with $k>0$ arms and $n\ge k$, the sum of $\Delta_i\,\mathbb E[T_i(n)]$ over arms with $\Delta_i>8\sqrt{k/n}$ is at most $\sum_i(\Delta_i+15\sqrt{n/k})$ over the same filtered set. The source proves the armwise estimate using $T_i(n)\le\kappa_i$ and Lemma 8.2, then sums it.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), proof of Theorem 9.1, printed pp. 126-127 / PDF pp. 135-136: definition of kappa_i, Lemma 8.2 armwise bound, and displayed large-gap sum.

import Definitions.Def_banditRegret
import Definitions.Def_mossPolicy

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.moss_large_gap_occupation_sum_bound
    {k : ℕ} (hk : 0 < k)
    {ν : BanditAlgorithm.StochasticBandit k}
    (hν : BanditAlgorithm.IsSubgaussianBandit 1 ν)
    {n : ℕ} {π : BanditAlgorithm.BanditPolicy k}
    (hπ : BanditAlgorithm.IsMOSSPolicy n π) (hkn : k ≤ n) :
    Finset.sum
        (Finset.univ.filter
          (fun i ↦ 8 * Real.sqrt ((k : ℝ) / n) < BanditAlgorithm.banditGap ν i))
        (fun i ↦ BanditAlgorithm.banditGap ν i *
          MeasureTheory.integral
            (BanditAlgorithm.banditMeasure ν π n)
            (fun h ↦ (BanditAlgorithm.armPullCount i h : ℝ))) ≤
      Finset.sum
        (Finset.univ.filter
          (fun i ↦ 8 * Real.sqrt ((k : ℝ) / n) < BanditAlgorithm.banditGap ν i))
        (fun i ↦ BanditAlgorithm.banditGap ν i +
          15 * Real.sqrt ((n : ℝ) / k)) := by
  sorry
