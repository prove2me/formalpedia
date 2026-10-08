-- Prove2me | Theorems.Thm_AvgCompletionSched_ParallelRelease_two_sqrt_two_approx
-- name    : AvgCompletionSched.ParallelRelease.two_sqrt_two_approx
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T19:59:02.408114+00:00
-- url     : https://prove2.me/theorems/24146161-0637-46dd-8d19-10056d48f66a
-- title:
--   Lemma 4.19 — the better of list scheduling and Delay List from $P1$ is a $2\sqrt2\approx2.83$-approximation
-- statement:
--   Let $I$ be an instance of nonpreemptive scheduling on $m\ge1$ identical machines with release dates, minimizing total completion time. Let $P1$ be an optimal preemptive schedule of the one-machine relaxation $I1$ (processing times $p_j/m$, release dates $r_j$), and let $\pi$ list the jobs in nondecreasing order of $C^{P1}_j$. Let $N$ be the strict-order list schedule of $\pi$, and let $D$ be a schedule produced by the continuous-time Delay List algorithm on $\pi$ with parameter
--   $$\beta_0=\sqrt{3-2\sqrt2}.$$
--   Then for every feasible nonpreemptive schedule of $I$ with completion times $C^*_j$,
--   $$\min\Bigl(\sum_j C^N_j,\ \sum_j C^D_j\Bigr)\le 2\sqrt2\,\sum_j C^*_j.$$
--
--   This is Lemma 4.19: running both algorithms and keeping the better schedule is a $2\sqrt2\approx2.83$-approximation for average completion time on parallel machines with release dates, improving the ratio $2.89+\epsilon$ of Chakrabarti et al. and the $(3-1/m)$ of Lemma 3.2.
--
--   **Formalization Note** The printed lemma states the constant $2.83$; its proof establishes $2\sqrt2\approx2.8284$, which is stated here and implies the printed bound. "An appropriate choice of $\beta$" is the single value $\beta_0$ that the proof's algorithm runs. The running time $O(n\log n)$ is not part of the statement. $\sum_j C^*_j$ ranges over every feasible schedule instead of an optimal one, which is equivalent. For $m=1$ the list schedule alone meets the bound.
-- source:
--   Chekuri, Motwani, Natarajan, Stein, Approximation Techniques for Average Completion Time Scheduling, SIAM J. Comput. 31(1), 2001, p. 163, Lemma 4.19 (constant 2√2 and β = √(3 − 2√2) from its proof, p. 164)

import Mathlib
import Definitions.Def_AvgCompletionSched_ParallelRelease_Model
import Definitions.Def_AvgCompletionSched_ParallelRelease_DelayList

namespace AvgCompletionSched.ParallelRelease

/-- Lemma 4.19 (with the constant `2√2 ≈ 2.8284 < 2.83` of its proof): let `P1` be an optimal
preemptive schedule of the one-machine relaxation, `π` the list of jobs in order of completion in
`P1`, `N` the strict-order list schedule of `π`, and `D` a Delay List schedule on `π` with
`β = √(3 - 2√2)`. Then the better of `N` and `D` has total completion time at most `2√2` times
that of every feasible nonpreemptive schedule. -/
theorem two_sqrt_two_approx {n m : ℕ} (I : Instance n m) (P1 : RelaxSchedule I)
    (hP1 : P1.IsOptimal) (π : Fin n ≃ Fin n) (hπ : IsCompletionOrder P1 π)
    (D : DelayListRun I) (hD : IsDelayListSchedule I π (Real.sqrt (3 - 2 * Real.sqrt 2)) D)
    (Nstar : Schedule I) :
    min (∑ j, listCompletion I π j) (∑ j, D.C j) ≤ 2 * Real.sqrt 2 * ∑ j, Nstar.C j := by sorry

end AvgCompletionSched.ParallelRelease
