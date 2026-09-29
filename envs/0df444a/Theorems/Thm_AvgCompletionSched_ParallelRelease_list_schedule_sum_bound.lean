-- Prove2me | Theorems.Thm_AvgCompletionSched_ParallelRelease_list_schedule_sum_bound
-- name    : AvgCompletionSched.ParallelRelease.list_schedule_sum_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T19:54:36.134986+00:00
-- url     : https://prove2.me/theorems/e9352715-1807-489f-b8a4-3d94d9b0ec3c
-- title:
--   (3.3) — $\sum_j C^N_j\le 2\sum_j C^{P1}_j+(1-1/m)\sum_j p_j$
-- statement:
--   Let $P1$ be any preemptive schedule of the one-machine relaxation $I1$ (processing times $p_j/m$, release dates $r_j$), let $\pi$ be a list of the jobs in nondecreasing order of their completion times $C^{P1}_j$, and let $N$ be the schedule produced by strict-order list scheduling of $\pi$ on the $m$ machines. Then
--   $$\sum_j C^N_j\le 2\sum_j C^{P1}_j+\Bigl(1-\frac1m\Bigr)\sum_j p_j.$$
--
--   This is inequality (3.3), obtained by summing the per-job bound (3.2) over all jobs. Together with Lemma 3.1 it yields the $(3-1/m)$-approximation of Lemma 3.2, and it is re-used as (4.1) in the proof of Lemma 4.19.
--
--   **Formalization Note** $P1$ need not be optimal here. Ties in the completion order are arbitrary: the statement holds for every list consistent with the completion times.
-- source:
--   Chekuri, Motwani, Natarajan, Stein, Approximation Techniques for Average Completion Time Scheduling, SIAM J. Comput. 31(1), 2001, p. 157, proof of Lemma 3.2, eq. (3.3) (with (3.1), (3.2))

import Mathlib
import Definitions.Def_AvgCompletionSched_ParallelRelease_Model

namespace AvgCompletionSched.ParallelRelease

/-- (3.3): for any preemptive schedule `P1` of `I1` and any list `π` ordering the jobs by their
completion times in `P1`, the strict-order list schedule `N` satisfies
`∑ C^N_j ≤ 2 ∑ C^{P1}_j + (1 - 1/m) ∑ p_j`. -/
theorem list_schedule_sum_bound {n m : ℕ} (I : Instance n m) (P1 : RelaxSchedule I)
    (π : Fin n ≃ Fin n) (hπ : IsCompletionOrder P1 π) :
    ∑ j, listCompletion I π j ≤
      2 * ∑ j, P1.CP j + (1 - (1 : ℝ) / m) * ∑ j, I.p j := by sorry

end AvgCompletionSched.ParallelRelease
