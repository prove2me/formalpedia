-- Prove2me | Theorems.Thm_AvgCompletionSched_ParallelRelease_delay_list_balanced_bound
-- name    : AvgCompletionSched.ParallelRelease.delay_list_balanced_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T19:58:13.80187+00:00
-- url     : https://prove2.me/theorems/81537b2e-57a5-4ac2-b7ac-a00877efe389
-- title:
--   Delay List when $\sum_j p_j>\alpha\sum_j C^*_j$: $\sum_j C^D_j\le(2+\beta+(1-\alpha)/\beta)\sum_j C^*_j$
-- statement:
--   Under the hypotheses of Lemma 4.18 ($m\ge2$, $\beta>0$, $P1$ an optimal preemptive schedule of $I1$, $\pi$ its completion order, $D$ a Delay List schedule with parameter $\beta$ on $\pi$), let $N^*$ be a feasible nonpreemptive schedule of $I$ with completion times $C^*_j$ and let $\alpha$ be a real number with $\sum_j p_j>\alpha\sum_j C^*_j$. Then
--   $$\sum_j C^D_j\le\Bigl(2+\beta+\frac{1-\alpha}{\beta}\Bigr)\sum_j C^*_j.$$
--
--   This is the first display on p. 164, obtained by plugging (4.2) into Lemma 4.18. Choosing $\beta=\sqrt{1-\alpha}$ gives the ratio $2+2\sqrt{1-\alpha}$, which is balanced against the ratio $2+\alpha$ of list scheduling in Lemma 4.19.
-- source:
--   Chekuri, Motwani, Natarajan, Stein, Approximation Techniques for Average Completion Time Scheduling, SIAM J. Comput. 31(1), 2001, p. 164, proof of Lemma 4.19, first display

import Mathlib
import Definitions.Def_AvgCompletionSched_ParallelRelease_Model
import Definitions.Def_AvgCompletionSched_ParallelRelease_DelayList

namespace AvgCompletionSched.ParallelRelease

/-- The balanced bound (p. 164): if moreover `∑ p_j > α ∑ C*_j`, then
`∑ C^D_j ≤ (2 + β + (1 - α)/β) ∑ C*_j`. -/
theorem delay_list_balanced_bound {n m : ℕ} (I : Instance n m) (hm : 2 ≤ m)
    (P1 : RelaxSchedule I) (hP1 : P1.IsOptimal) (π : Fin n ≃ Fin n)
    (hπ : IsCompletionOrder P1 π) (β : ℝ) (hβ : 0 < β) (D : DelayListRun I)
    (hD : IsDelayListSchedule I π β D) (Nstar : Schedule I) (α : ℝ)
    (hα : α * ∑ j, Nstar.C j < ∑ j, I.p j) :
    ∑ j, D.C j ≤ (2 + β + (1 - α) / β) * ∑ j, Nstar.C j := by sorry

end AvgCompletionSched.ParallelRelease
