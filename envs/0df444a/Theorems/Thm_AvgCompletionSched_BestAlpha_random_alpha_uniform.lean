-- Prove2me | Theorems.Thm_AvgCompletionSched_BestAlpha_random_alpha_uniform
-- name    : AvgCompletionSched.BestAlpha.random_alpha_uniform
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T19:49:57.864983+00:00
-- url     : https://prove2.me/theorems/d651ea8e-cb61-4313-8a1a-a2b4d18a7ddf
-- title:
--   Theorem 2.6.1 — Random-$\alpha$ with uniform $\alpha$ has expected ratio at most $2$
-- statement:
--   Consider one-machine scheduling with release dates to minimize weighted completion time: processing times $p_j>0$, release dates $r_j\ge0$, weights $w_j>0$. Let $P$ be a preemptive schedule that is optimal among all preemptive schedules for $\sum_j w_jC_j$. If $\alpha$ is chosen uniformly in $(0,1]$ and $C^\alpha_j$ is the completion time of $J_j$ in the $\alpha$-schedule derived from $P$ (ties broken by job index), then for every feasible nonpreemptive schedule with completion times $C_j$,
--   $$E\Bigl[\sum_j w_jC^\alpha_j\Bigr]=\int_0^1\sum_j w_jC^\alpha_j\,d\alpha\le 2\sum_j w_jC_j ,$$
--   and the integrand is integrable. That is, the expected approximation ratio of Random-$\alpha$ with uniform $\alpha$ is at most $2$.
--
--   **Formalization Note** "Approximation ratio" is stated as the inequality against every feasible nonpreemptive schedule. The optimality of $P$ among preemptive schedules is the paper's standing assumption for its upper bounds (p. 151).
-- source:
--   Chekuri, Motwani, Natarajan, Stein, Approximation Techniques for Average Completion Time Scheduling, SIAM J. Comput. 31(1), 2001, p. 154, Theorem 2.6, part 1; standing assumption p. 151

import Mathlib
import Definitions.Def_AvgCompletionSched_BestAlpha_Model

namespace AvgCompletionSched.BestAlpha
theorem random_alpha_uniform {n : ℕ} {I : Instance n} (w : Fin n → ℝ) (hw : ∀ j, 0 < w j)
    (P : PreemptiveSchedule I)
    (hP : ∀ P' : PreemptiveSchedule I, ∑ j, w j * P.CP j ≤ ∑ j, w j * P'.CP j)
    (N : NonpreemptiveSchedule I) :
    IntervalIntegrable (fun α => ∑ j, w j * P.Calpha α j) MeasureTheory.volume 0 1 ∧
      ∫ α in (0 : ℝ)..1, ∑ j, w j * P.Calpha α j ≤ 2 * ∑ j, w j * N.C j := by sorry
end AvgCompletionSched.BestAlpha
