-- Prove2me | Theorems.Thm_BanditAlgorithm_ucb_suboptimal_arm_good_event
-- name    : BanditAlgorithm.ucb_suboptimal_arm_good_event
-- status  : Proved
-- author  : @allychan327
-- created : 2026-07-18T22:13:20.976158+00:00
-- url     : https://prove2.me/theorems/dd501a0e-c889-4a2a-b2a6-7a9385f439a2
-- title:
--   UCB suboptimal-arm good event (Eqs. 7.6–7.10)
-- statement:
--   For UCB with confidence level $\delta=1/n^2$ on a finite 1-subgaussian stochastic bandit and a suboptimal arm $i$, let $u=\lceil16\log(n)/\Delta_i^2\rceil$. There is a measurable good event on which $T_i(n)\le u$, while the complement has probability at most $1/n+1/n^2$. This is the good-event and concentration core of Eqs. (7.6)–(7.10), including the $n=1$ boundary.
-- source:
--   Lattimore--Szepesvari, Bandit Algorithms (CUP 2020), proof of Theorem 7.1, printed pp. 106--108 (PDF pp. 115--117), Eqs. (7.6)--(7.10), specialized to delta=1/n^2 and c=1/2; https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_banditRegret
import Definitions.Def_ucbPolicy

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

/-!
Source: Lattimore--Szepesvári, *Bandit Algorithms* (CUP 2020), proof of
Theorem 7.1, printed pp. 106--108 (PDF pp. 115--117), Eqs. (7.6)--(7.10).

This isolates the substantive good-event step in the UCB pull-count proof at
`δ = 1 / n²` and `c = 1/2`.  On the good event the suboptimal arm is pulled at
most `⌈16 log(n) / Δᵢ²⌉` times, while the union bound and fixed-sample
subgaussian estimates bound the complement by `1/n + 1/n²`.

The statement explicitly includes `n = 1`.  In that boundary case the bound on
the bad event is at least one, so an empty good event witnesses the claim.
-/

theorem ucb_suboptimal_arm_good_event
    {k : ℕ} (hk : 0 < k) {ν : StochasticBandit k}
    (hν : IsSubgaussianBandit 1 ν) {n : ℕ} (hn : 0 < n)
    {π : BanditPolicy k} (hπ : IsUCBPolicy (1 / (n : ℝ) ^ 2) π)
    (i : Fin k) (hi : 0 < banditGap ν i) :
    let u : ℕ := ⌈16 * Real.log n / (banditGap ν i) ^ 2⌉₊
    ∃ G : Set (BanditHistory k n),
      MeasurableSet G ∧
      (∀ h ∈ G, armPullCount i h ≤ u) ∧
      (banditMeasure ν π n).real Gᶜ ≤
        1 / (n : ℝ) + 1 / (n : ℝ) ^ 2 := by
  sorry

end BanditAlgorithm
