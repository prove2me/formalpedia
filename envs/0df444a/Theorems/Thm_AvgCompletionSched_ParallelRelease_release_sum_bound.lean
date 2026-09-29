-- Prove2me | Theorems.Thm_AvgCompletionSched_ParallelRelease_release_sum_bound
-- name    : AvgCompletionSched.ParallelRelease.release_sum_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T19:55:43.934982+00:00
-- url     : https://prove2.me/theorems/e8792d8a-a11f-4582-8ab5-7d90852a163d
-- title:
--   (4.2) — if $\sum_j p_j>\alpha\sum_j C^*_j$ then $\sum_j r_j\le(1-\alpha)\sum_j C^*_j$
-- statement:
--   Let $N^*$ be a feasible nonpreemptive schedule of an instance on $m$ machines with release dates, with completion times $C^*_j$, and let $\alpha$ be a real number. If
--   $$\sum_j p_j>\alpha\sum_j C^*_j,\qquad\text{then}\qquad\sum_j r_j\le(1-\alpha)\sum_j C^*_j.$$
--
--   This is inequality (4.2). It follows from the simple bound $\sum_j C^*_j\ge\sum_j(p_j+r_j)$ and is the case split that lets the analysis of Lemma 4.19 balance list scheduling against Delay List: when the processing times are small relative to the optimum, list scheduling is good; otherwise the release dates are small, which is what Delay List needs.
-- source:
--   Chekuri, Motwani, Natarajan, Stein, Approximation Techniques for Average Completion Time Scheduling, SIAM J. Comput. 31(1), 2001, p. 163, proof of Lemma 4.19, eq. (4.2)

import Mathlib
import Definitions.Def_AvgCompletionSched_ParallelRelease_Model

namespace AvgCompletionSched.ParallelRelease

/-- (4.2): if `∑ p_j > α ∑ C*_j`, then `∑ r_j ≤ (1 - α) ∑ C*_j`. -/
theorem release_sum_bound {n m : ℕ} (I : Instance n m) (Nstar : Schedule I) (α : ℝ)
    (hα : α * ∑ j, Nstar.C j < ∑ j, I.p j) :
    ∑ j, I.r j ≤ (1 - α) * ∑ j, Nstar.C j := by sorry

end AvgCompletionSched.ParallelRelease
