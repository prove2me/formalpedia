-- Prove2me | Theorems.Thm_AvgCompletionSched_InTree_list_schedule_completion_bound
-- name    : AvgCompletionSched.InTree.list_schedule_completion_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T20:09:40.485988+00:00
-- url     : https://prove2.me/theorems/7d885bc2-1c84-44d1-a2b1-51cab3102f0a
-- title:
--   Lemma 4.16 — $C^m_i \le \kappa_i + C^1_i/m$ for list scheduling on in-trees
-- statement:
--   Let an in-tree instance without release dates and a number $m\ge 1$ of machines be given. Let $\pi$ be a list of the jobs obeying the precedence constraints, and $S^1$ the one-machine schedule that processes the jobs in the order $\pi$ without idle time, with completion times $C^1_i$. If $S^m$ is a list schedule on $m$ machines using $\pi$ as the list (Graham's rule), then for every job $J_i$
--   $$C^m_i\le \kappa_i+\frac{C^1_i}{m}.$$
--
--   This per-job bound is the key step of the 2-approximation for in-trees: summing it with weights and applying Lemmas 4.10 and 4.11 gives Theorem 4.17.
--
--   **Formalization Note** The in-tree hypothesis and the absence of release dates are standing assumptions of §4.4 and are part of the instance. The one-machine schedule need not be optimal. It is taken idle-free, as the paper's proof assumes ("since there are no release dates, we can assume that the schedule $S^1$ has no idle time").
-- source:
--   Chekuri, Motwani, Natarajan, Stein, Approximation Techniques for Average Completion Time Scheduling, SIAM J. Comput. 31(1), 2001, p. 162, Lemma 4.16 (proof pp. 162–163)

import Mathlib
import Definitions.Def_AvgCompletionSched_InTree_Model
import Definitions.Def_AvgCompletionSched_InTree_ListScheduling

namespace AvgCompletionSched.InTree

/-- Lemma 4.16 (p. 162): if `G` is the list schedule on `m` machines using a one-machine
schedule `S¹` (the idle-free schedule in the order `π`) as the list, then for every job `i`,
`C^m_i ≤ κ_i + C^1_i / m`. -/
theorem list_schedule_completion_bound {n : ℕ} (I : Instance n) (m : ℕ) (hm : 1 ≤ m)
    (π : Fin n ≃ Fin n) (hπ : ObeysPrecedence I π) (G : Schedule I m)
    (hG : IsListSchedule I π G) (i : Fin n) :
    G.C i ≤ kappa I i + oneMachineC I π i / (m : ℝ) := by sorry

end AvgCompletionSched.InTree
