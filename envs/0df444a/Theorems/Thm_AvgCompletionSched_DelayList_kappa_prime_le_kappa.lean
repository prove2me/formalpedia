-- Prove2me | Theorems.Thm_AvgCompletionSched_DelayList_kappa_prime_le_kappa
-- name    : AvgCompletionSched.DelayList.kappa_prime_le_kappa
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T20:02:20.254986+00:00
-- url     : https://prove2.me/theorems/c62f8fb1-a9d7-44f7-a043-f57752dde0af
-- title:
--   Fact 4.5 — $\kappa'_i \le \kappa_i$
-- statement:
--   Let $S^m$ be a schedule produced by the continuous-time algorithm Delay List with parameter $\beta>0$ on $m\ge 2$ machines, using a list that obeys the precedence constraints. For every job $J_i$ and every path $P'_i$ of Definition 4.4, with length $\kappa'_i=r_{j_1}+\sum_k p_{j_k}$,
--   $$\kappa'_i\le\kappa_i,$$
--   where $\kappa_i$ is the critical-path length of Definition 4.1.
--
--   The path $P'_i$ is built from the schedule, while $\kappa_i$ depends only on the instance; this fact lets the schedule-dependent bounds of Lemma 4.8 and Theorem 4.9 be stated in terms of $\kappa_i$.
-- source:
--   Chekuri, Motwani, Natarajan, Stein, Approximation Techniques for Average Completion Time Scheduling, SIAM J. Comput. 31(1), 2001, p. 159, Fact 4.5

import Mathlib
import Definitions.Def_AvgCompletionSched_DelayList_Model
import Definitions.Def_AvgCompletionSched_DelayList_Algorithm
import Definitions.Def_AvgCompletionSched_DelayList_Analysis

namespace AvgCompletionSched.DelayList

/-- Fact 4.5 (p. 159): `κ′_i ≤ κ_i`, for every path `P′_i` of Definition 4.4 in a Delay List
schedule. -/
theorem kappa_prime_le_kappa {n m : ℕ} (I : Instance n) (hm : 2 ≤ m) (π : Fin n ≃ Fin n)
    (hπ : ObeysPrecedence I π) (β : ℝ) (hβ : 0 < β) (D : DelayListRun I m)
    (hD : IsDelayListSchedule I m π β D) (i j₁ : Fin n) (l : List (Fin n))
    (hP : D.IsPathPrime i j₁ l) :
    kappaPrime I j₁ l ≤ kappa I i := by sorry

end AvgCompletionSched.DelayList
