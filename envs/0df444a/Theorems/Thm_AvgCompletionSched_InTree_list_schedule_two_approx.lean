-- Prove2me | Theorems.Thm_AvgCompletionSched_InTree_list_schedule_two_approx
-- name    : AvgCompletionSched.InTree.list_schedule_two_approx
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T20:11:25.691089+00:00
-- url     : https://prove2.me/theorems/bda03b9a-4e85-4f2f-bee0-da441435a983
-- title:
--   Theorem 4.17 — list scheduling from an optimal one-machine schedule is a 2-approximation for in-trees
-- statement:
--   Consider nonpreemptive scheduling of $n$ jobs with processing times $p_j>0$ and weights $w_j>0$ on $m\ge 1$ identical machines, under in-tree precedence constraints and without release dates. Let $\pi$ be an optimal one-machine schedule, and let $G$ be Graham's list schedule on $m$ machines using $\pi$ as the list. Then for every feasible nonpreemptive $m$-machine schedule $N$
--   $$\sum_j w_j C^G_j\le 2\sum_j w_j C^N_j .$$
--   That is, list scheduling from an optimal one-machine schedule has approximation ratio 2 for minimizing weighted completion time on $m$ machines for in-tree precedence without release dates.
--
--   For in-trees this improves the ratio 4 that the general conversion (Delay List with $\beta=1$) gives from an optimal one-machine schedule.
--
--   **Formalization Note** The theorem's claim that the algorithm runs in $O(n\log n)$ time (dominated by computing the optimal one-machine schedule with the algorithm of reference [1]) is not stated; the optimal one-machine schedule is a hypothesis, and its existence is a separate item. The algorithm is the paper's (§4.4); an existential "there is an algorithm" statement would be trivially true. The ratio is stated against every feasible schedule rather than an infimum.
-- source:
--   Chekuri, Motwani, Natarajan, Stein, Approximation Techniques for Average Completion Time Scheduling, SIAM J. Comput. 31(1), 2001, p. 162, Theorem 4.17 (proof p. 163); algorithm from §4.4, p. 162

import Mathlib
import Definitions.Def_AvgCompletionSched_InTree_Model
import Definitions.Def_AvgCompletionSched_InTree_ListScheduling

namespace AvgCompletionSched.InTree

/-- Theorem 4.17 (p. 162): list scheduling on `m` machines, using an optimal one-machine
schedule as the list, is a 2-approximation for minimizing weighted completion time with in-tree
precedence and no release dates: its value is at most twice that of every feasible `m`-machine
schedule. -/
theorem list_schedule_two_approx {n : ℕ} (I : Instance n) (m : ℕ) (hm : 1 ≤ m)
    (π : Fin n ≃ Fin n) (hπ : IsOptimalOneMachine I π) (G : Schedule I m)
    (hG : IsListSchedule I π G) (N : Schedule I m) :
    G.wct ≤ 2 * N.wct := by sorry

end AvgCompletionSched.InTree
