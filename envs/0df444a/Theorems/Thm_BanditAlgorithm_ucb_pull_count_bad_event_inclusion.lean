-- Prove2me | Theorems.Thm_BanditAlgorithm_ucb_pull_count_bad_event_inclusion
-- name    : BanditAlgorithm.ucb_pull_count_bad_event_inclusion
-- status  : Proved
-- author  : @allychan327
-- created : 2026-07-19T02:44:06.898051+00:00
-- url     : https://prove2.me/theorems/637edc5b-23ed-4bb0-aa1f-8a247b27a8b5
-- title:
--   UCB pull-count bad-event inclusion
-- statement:
--   Fix a suboptimal arm and an optimal arm. On almost every canonical UCB history, if the suboptimal arm is pulled more than the cap $u=\lceil16\log(n)/\Delta_i^2\rceil$, then either an optimal-arm lower-confidence failure occurs at one of the first $n$ sample counts or the stopped centered reward of the suboptimal arm exceeds $u\Delta_i/2$. This is the deterministic UCB-index contradiction that produces the two events in Eq. (7.6).
-- source:
--   Lattimore--Szepesvari, Bandit Algorithms (CUP 2020), proof of Theorem 7.1, printed pp. 105--107 (PDF pp. 114--116), the UCB-index contradiction preceding Eq. (7.6) and Eqs. (7.6)--(7.8); https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_ucbStoppedCenteredSum
import Definitions.Def_ucbPolicy

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

/-!
Source: Lattimore--Szepesvári, *Bandit Algorithms* (CUP 2020), proof of
Theorem 7.1, printed pp. 105--107 (PDF pp. 114--116), especially the UCB-index
contradiction preceding Eq. (7.6) and the two bad events in Eqs. (7.6)--(7.8).
-/

theorem ucb_pull_count_bad_event_inclusion
    {k : ℕ} (hk : 0 < k) {ν : StochasticBandit k}
    {n : ℕ} (hn : 0 < n) (hkn : k < n)
    {π : BanditPolicy k} (hπ : IsUCBPolicy (1 / (n : ℝ) ^ 2) π)
    (i : Fin k) (hi : 0 < banditGap ν i) :
    ∃ j : Fin k, banditArmMean ν j = banditOptimalMean ν ∧
      let u : ℕ := ⌈16 * Real.log n / (banditGap ν i) ^ 2⌉₊
      let optBad : Fin n → Set (BanditHistory k n) := fun r ↦
        let s : ℕ := r + 1
        let t : ℝ := Real.sqrt
          (2 * Real.log ((n : ℝ) ^ 2) / (s : ℝ))
        {h | armStoppedCenteredSum ν j s n h ≤ -(s : ℝ) * t}
      let subBad : Set (BanditHistory k n) :=
        {h | (u : ℝ) * (banditGap ν i / 2) ≤
          armStoppedCenteredSum ν i u n h}
      ∀ᵐ h ∂banditMeasure ν π n,
        u < armPullCount i h → h ∈ ((⋃ r, optBad r) ∪ subBad) := by
  sorry

end BanditAlgorithm
