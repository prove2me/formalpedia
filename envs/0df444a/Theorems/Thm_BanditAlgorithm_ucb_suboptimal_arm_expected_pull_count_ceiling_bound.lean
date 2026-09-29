-- Prove2me | Theorems.Thm_BanditAlgorithm_ucb_suboptimal_arm_expected_pull_count_ceiling_bound
-- name    : BanditAlgorithm.ucb_suboptimal_arm_expected_pull_count_ceiling_bound
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-07-18T21:44:24.126253+00:00
-- url     : https://prove2.me/theorems/4374abcc-50ba-4c06-b45a-176280f8d340
-- title:
--   UCB pull-count ceiling bound (Eq. 7.10)
-- statement:
--   For UCB at confidence level $\delta=1/n^2$ on a finite 1-subgaussian stochastic bandit, the expected number of pulls of any suboptimal arm $i$ is at most $\lceil 16\log(n)/\Delta_i^2\rceil+1+1/n$. This is the pre-rounding estimate in the proof of Theorem 7.1. The $n=1$ case is included explicitly by the formal statement.
-- source:
--   Lattimore--Szepesvari, Bandit Algorithms (CUP 2020), proof of Theorem 7.1, printed pp. 105--108 (PDF pp. 114--117), Eqs. (7.5)--(7.10), especially Eq. (7.10) after choosing c=1/2; https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_banditRegret
import Definitions.Def_ucbPolicy

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

/-!
Source: Lattimore--Szepesvári, *Bandit Algorithms* (CUP 2020), proof of
Theorem 7.1, printed pp. 105--108 (PDF pp. 114--117), especially Eqs.
(7.5)--(7.10). This is Eq. (7.10) after setting `δ = 1 / n²` and `c = 1/2`;
the source's final display then uses `ceil x ≤ x + 1` and `1 / n ≤ 1`.

The `n = 1` boundary is included: the displayed right side is then `2`, while
the pull count is at most one. The positive-gap hypothesis makes the denominator
nonzero, and `hn` makes the reciprocal horizon well-defined.
-/

theorem ucb_suboptimal_arm_expected_pull_count_ceiling_bound
    {k : ℕ} (hk : 0 < k) {ν : StochasticBandit k}
    (hν : IsSubgaussianBandit 1 ν) {n : ℕ} (hn : 0 < n)
    {π : BanditPolicy k} (hπ : IsUCBPolicy (1 / (n : ℝ) ^ 2) π)
    (i : Fin k) (hi : 0 < banditGap ν i) :
    ∫ h, (armPullCount i h : ℝ) ∂(banditMeasure ν π n) ≤
      ((⌈16 * Real.log n / (banditGap ν i) ^ 2⌉₊ : ℕ) : ℝ) +
        1 + 1 / (n : ℝ) := by
  sorry

end BanditAlgorithm
