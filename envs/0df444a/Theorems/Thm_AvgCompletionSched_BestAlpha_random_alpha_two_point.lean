-- Prove2me | Theorems.Thm_AvgCompletionSched_BestAlpha_random_alpha_two_point
-- name    : AvgCompletionSched.BestAlpha.random_alpha_two_point
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T19:50:29.434446+00:00
-- url     : https://prove2.me/theorems/19117091-114f-4787-b8a6-32838eed4dd0
-- title:
--   Theorem 2.6.2 — $\alpha=1$ w.p. $3/5$, $\alpha=1/2$ w.p. $2/5$ gives expected ratio at most $1.8$
-- statement:
--   Consider one-machine scheduling with release dates to minimize weighted completion time: processing times $p_j>0$, release dates $r_j\ge0$, weights $w_j>0$. Let $P$ be a preemptive schedule that is optimal among all preemptive schedules for $\sum_j w_jC_j$. Let $C^{1}_j$ be the completion times of any $1$-schedule and $C^{1/2}_j$ those of any $\tfrac12$-schedule derived from $P$ (ties among equal $\alpha$-points in any order). Then for every feasible nonpreemptive schedule with completion times $C_j$,
--   $$\frac35\sum_j w_jC^{1}_j+\frac25\sum_j w_jC^{1/2}_j\le 1.8\sum_j w_jC_j .$$
--   That is, choosing $\alpha=1$ with probability $3/5$ and $\alpha=1/2$ with probability $2/5$ gives expected approximation ratio at most $1.8$; in particular, one of the two schedules is within $1.8$ of optimal.
--
--   **Formalization Note** The paper omits the proof of this part. The expectation over the two-point distribution is written out as the weighted average. "Approximation ratio" is stated as the inequality against every feasible nonpreemptive schedule.
-- source:
--   Chekuri, Motwani, Natarajan, Stein, Approximation Techniques for Average Completion Time Scheduling, SIAM J. Comput. 31(1), 2001, p. 154, Theorem 2.6, part 2 (proof omitted in the paper); standing assumption p. 151

import Mathlib
import Definitions.Def_AvgCompletionSched_BestAlpha_Model

namespace AvgCompletionSched.BestAlpha
theorem random_alpha_two_point {n : ℕ} {I : Instance n} (w : Fin n → ℝ) (hw : ∀ j, 0 < w j)
    (P : PreemptiveSchedule I)
    (hP : ∀ P' : PreemptiveSchedule I, ∑ j, w j * P.CP j ≤ ∑ j, w j * P'.CP j)
    (π₁ π₂ : Fin n ≃ Fin n) (hπ₁ : IsAlphaOrder P 1 π₁) (hπ₂ : IsAlphaOrder P (1 / 2) π₂)
    (N : NonpreemptiveSchedule I) :
    3 / 5 * ∑ j, w j * listCompletion I π₁ j + 2 / 5 * ∑ j, w j * listCompletion I π₂ j
      ≤ 9 / 5 * ∑ j, w j * N.C j := by sorry
end AvgCompletionSched.BestAlpha
