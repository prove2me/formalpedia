-- Prove2me | Theorems.Thm_BanditAlgorithm_ucb_suboptimal_arm_pull_count_tail
-- name    : BanditAlgorithm.ucb_suboptimal_arm_pull_count_tail
-- status  : Proved
-- author  : @MKPynnic
-- created : 2026-07-18T23:45:50.523662+00:00
-- url     : https://prove2.me/theorems/df105b6b-7fac-4520-9b67-ced70ad783cc
-- title:
--   UCB suboptimal-arm pull-count tail
-- statement:
--   For a finite 1-subgaussian stochastic bandit, UCB at confidence level $\delta=1/n^2$, a suboptimal arm $i$, and a post-initialization horizon $k<n$, the probability that the arm is pulled more than $\lceil16\log(n)/\Delta_i^2\rceil$ times is at most $1/n+1/n^2$. This is the concrete adaptive-sampling tail estimate obtained from the two failure events in Eqs. (7.6)--(7.10); unlike the parent good-event statement, it exposes the reusable pull-count probability inequality directly.
-- source:
--   Lattimore--Szepesvari, Bandit Algorithms (CUP 2020), proof of Theorem 7.1, printed pp. 106--108 (PDF pp. 115--117), Eqs. (7.6)--(7.10), using the reward-stack model in Section 4.6, printed p. 65 (PDF p. 74), and the bounded optional-stopping hint in Exercise 4.4, printed p. 69 (PDF p. 78); https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_banditRegret
import Definitions.Def_ucbPolicy

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

/-!
Source: Lattimore--Szepesvári, *Bandit Algorithms* (CUP 2020), proof of
Theorem 7.1, printed pp. 106--108 (PDF pp. 115--117), Eqs. (7.6)--(7.10),
using the reward-stack model from §4.6, printed p. 65 (PDF p. 74), and the
bounded optional-stopping bridge in Exercise 4.4, printed p. 69 (PDF p. 78).

This is the concrete post-initialization pull-count tail estimate. It is the
probabilistic core used both to construct the UCB good event and to control the
expected number of pulls of a suboptimal arm.
-/

theorem ucb_suboptimal_arm_pull_count_tail
    {k : ℕ} (hk : 0 < k) {ν : StochasticBandit k}
    (hν : IsSubgaussianBandit 1 ν) {n : ℕ} (hn : 0 < n) (hkn : k < n)
    {π : BanditPolicy k} (hπ : IsUCBPolicy (1 / (n : ℝ) ^ 2) π)
    (i : Fin k) (hi : 0 < banditGap ν i) :
    (banditMeasure ν π n).real
        {h : BanditHistory k n |
          ⌈16 * Real.log n / (banditGap ν i) ^ 2⌉₊ < armPullCount i h} ≤
      1 / (n : ℝ) + 1 / (n : ℝ) ^ 2 := by
  sorry

end BanditAlgorithm
