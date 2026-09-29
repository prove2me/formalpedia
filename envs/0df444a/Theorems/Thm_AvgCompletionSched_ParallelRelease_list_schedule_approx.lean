-- Prove2me | Theorems.Thm_AvgCompletionSched_ParallelRelease_list_schedule_approx
-- name    : AvgCompletionSched.ParallelRelease.list_schedule_approx
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T19:55:06.158987+00:00
-- url     : https://prove2.me/theorems/b47da7d2-94bf-421a-86c7-a90c667e4970
-- title:
--   Lemma 3.2 — list scheduling from $P1$ is a $(3-1/m)$-approximation
-- statement:
--   Let $P1$ be an optimal preemptive schedule of the one-machine relaxation $I1$, let $\pi$ list the jobs in nondecreasing order of $C^{P1}_j$, and let $N$ be the strict-order list schedule of $\pi$ on $m$ machines. Then for every feasible nonpreemptive schedule of $I$ with completion times $C^*_j$,
--   $$\sum_j C^N_j\le\Bigl(3-\frac1m\Bigr)\sum_j C^*_j.$$
--
--   This is Lemma 3.2: a simple $(3-1/m)$-approximation algorithm for average completion time on parallel machines with release dates, which uses neither linear programming nor dynamic programming. It is one of the two algorithms combined in Lemma 4.19.
--
--   **Formalization Note** $C^*$ ranges over every feasible schedule of $I$ instead of an optimal one, which is equivalent.
-- source:
--   Chekuri, Motwani, Natarajan, Stein, Approximation Techniques for Average Completion Time Scheduling, SIAM J. Comput. 31(1), 2001, p. 157, Lemma 3.2

import Mathlib
import Definitions.Def_AvgCompletionSched_ParallelRelease_Model

namespace AvgCompletionSched.ParallelRelease

/-- Lemma 3.2: list scheduling in the order of completion times of an optimal preemptive schedule
of `I1` is a `(3 - 1/m)`-approximation for total completion time. -/
theorem list_schedule_approx {n m : ℕ} (I : Instance n m) (P1 : RelaxSchedule I)
    (hP1 : P1.IsOptimal) (π : Fin n ≃ Fin n) (hπ : IsCompletionOrder P1 π)
    (Nstar : Schedule I) :
    ∑ j, listCompletion I π j ≤ (3 - (1 : ℝ) / m) * ∑ j, Nstar.C j := by sorry

end AvgCompletionSched.ParallelRelease
