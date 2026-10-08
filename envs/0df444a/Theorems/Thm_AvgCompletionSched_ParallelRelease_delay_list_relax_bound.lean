-- Prove2me | Theorems.Thm_AvgCompletionSched_ParallelRelease_delay_list_relax_bound
-- name    : AvgCompletionSched.ParallelRelease.delay_list_relax_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T19:57:37.36899+00:00
-- url     : https://prove2.me/theorems/d6a9d834-fb23-4922-bd94-79d79eeb1035
-- title:
--   Lemma 4.18 — Delay List on $P1$: $\sum_j C^D_j\le(2+\beta)\sum_j C^*_j+\frac1\beta\sum_j r_j$
-- statement:
--   Let $m\ge 2$ and $\beta>0$. Let $P1$ be an optimal preemptive schedule of the one-machine relaxation $I1$ (processing times $p_j/m$, release dates $r_j$), let $\pi$ list the jobs in nondecreasing order of $C^{P1}_j$, and let $D$ be a schedule produced by the continuous-time Delay List algorithm with parameter $\beta$ on $\pi$. Then for every feasible nonpreemptive schedule of $I$ with completion times $C^*_j$,
--   $$\sum_j C^D_j\le(2+\beta)\sum_j C^*_j+\frac1\beta\sum_j r_j.$$
--
--   This is Lemma 4.18. It is the Delay List half of the analysis of Lemma 4.19; the release-date term is controlled by (4.2).
--
--   **Formalization Note** The printed statement reads $(2+\beta)C^*_j$ without the sum; the last display of the proof has $(2+\beta)\sum_j C^*_j$, which is what is stated here.
-- source:
--   Chekuri, Motwani, Natarajan, Stein, Approximation Techniques for Average Completion Time Scheduling, SIAM J. Comput. 31(1), 2001, p. 163, Lemma 4.18

import Mathlib
import Definitions.Def_AvgCompletionSched_ParallelRelease_Model
import Definitions.Def_AvgCompletionSched_ParallelRelease_DelayList

namespace AvgCompletionSched.ParallelRelease

/-- Lemma 4.18: Delay List with parameter `β > 0` applied to the list of an optimal preemptive
schedule `P1` of `I1` gives `∑ C^D_j ≤ (2 + β) ∑ C*_j + (1/β) ∑ r_j`. -/
theorem delay_list_relax_bound {n m : ℕ} (I : Instance n m) (hm : 2 ≤ m)
    (P1 : RelaxSchedule I) (hP1 : P1.IsOptimal) (π : Fin n ≃ Fin n)
    (hπ : IsCompletionOrder P1 π) (β : ℝ) (hβ : 0 < β) (D : DelayListRun I)
    (hD : IsDelayListSchedule I π β D) (Nstar : Schedule I) :
    ∑ j, D.C j ≤ (2 + β) * ∑ j, Nstar.C j + 1 / β * ∑ j, I.r j := by sorry

end AvgCompletionSched.ParallelRelease
