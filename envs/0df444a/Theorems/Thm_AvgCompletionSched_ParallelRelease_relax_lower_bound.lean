-- Prove2me | Theorems.Thm_AvgCompletionSched_ParallelRelease_relax_lower_bound
-- name    : AvgCompletionSched.ParallelRelease.relax_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T19:54:02.575893+00:00
-- url     : https://prove2.me/theorems/6bd9c822-dc2f-454c-99dd-20c29a509094
-- title:
--   Lemma 3.1 — the one-machine relaxation lower-bounds the $m$-machine optimum
-- statement:
--   Let $I$ be an instance of nonpreemptive scheduling on $m$ identical machines with release dates, $I1$ its one-machine relaxation (processing times $p_j/m$, release dates $r_j$), and $P1$ an optimal preemptive schedule of $I1$. Then for every feasible nonpreemptive schedule $N^*$ of $I$ with completion times $C^*_j$,
--   $$\sum_j C^{P1}_j\le\sum_j C^*_j.$$
--
--   This is Lemma 3.1: the optimal value of $I1$ is a lower bound on the optimal value of $I$. It is the lower bound against which both the list schedule and Delay List are measured.
--
--   **Formalization Note** The optimum of $I$ is not written as an infimum: the bound is stated against every feasible schedule, which is equivalent. The statement combines Lemma 3.1 with the optimality of $P1$.
-- source:
--   Chekuri, Motwani, Natarajan, Stein, Approximation Techniques for Average Completion Time Scheduling, SIAM J. Comput. 31(1), 2001, p. 156, Lemma 3.1

import Mathlib
import Definitions.Def_AvgCompletionSched_ParallelRelease_Model

namespace AvgCompletionSched.ParallelRelease

/-- Lemma 3.1: the optimal value of the one-machine relaxation `I1` is at most the total
completion time of every feasible nonpreemptive `m`-machine schedule of `I`. -/
theorem relax_lower_bound {n m : ℕ} (I : Instance n m) (P1 : RelaxSchedule I)
    (hP1 : P1.IsOptimal) (Nstar : Schedule I) :
    ∑ j, P1.CP j ≤ ∑ j, Nstar.C j := by sorry

end AvgCompletionSched.ParallelRelease
