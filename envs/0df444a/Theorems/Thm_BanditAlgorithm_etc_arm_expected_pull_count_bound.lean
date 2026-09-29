-- Prove2me | Theorems.Thm_BanditAlgorithm_etc_arm_expected_pull_count_bound
-- name    : BanditAlgorithm.etc_arm_expected_pull_count_bound
-- status  : Proved
-- author  : @jianglsbz
-- created : 2026-07-19T05:16:49.908867+00:00
-- url     : https://prove2.me/theorems/64defa8c-5b4c-4e9c-af99-c68d1a62a325
-- statement:
--   Let a positive-number-of-arms stochastic bandit have 1-subgaussian rewards, and let an Explore-Then-Commit policy explore every arm exactly $m\ge 1$ times before committing, with $mk\le n$. For every arm $i$, its expected number of pulls through round $n$ is at most
--
--   $$m+(n-mk)\exp\!\left(-\frac{m\Delta_i^2}{4}\right).$$
--
--   For an optimal arm this specializes to the elementary horizon bound; for a suboptimal arm it combines the commit-count identity with the two-sample subgaussian comparison used in Theorem 6.1.
-- source:
--   Lattimore--Szepesvari, Bandit Algorithms (CUP 2020), Theorem 6.1 proof, printed pp. 92--93, Eqs. (6.2)--(6.3).

import Definitions.Def_banditRegret
import Definitions.Def_etcPolicy

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.etc_arm_expected_pull_count_bound {k : ℕ} (hk : 0 < k)
    {ν : StochasticBandit k} (hν : IsSubgaussianBandit 1 ν)
    {m n : ℕ} (hm : 1 ≤ m) (hmn : m * k ≤ n)
    {π : BanditPolicy k} (hπ : IsETCPolicy hk m π) (i : Fin k) :
    ∫ h, (armPullCount i h : ℝ) ∂(banditMeasure ν π n) ≤
      m + (n - m * k : ℝ) *
        Real.exp (-(m * (banditGap ν i) ^ 2) / 4) := by
  sorry
