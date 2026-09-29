-- Prove2me | Theorems.Thm_AvgCompletionSched_BestAlpha_random_alpha_exp
-- name    : AvgCompletionSched.BestAlpha.random_alpha_exp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T19:51:02.179992+00:00
-- url     : https://prove2.me/theorems/e5ddc447-4820-4f2a-a1b6-0a72e9103207
-- title:
--   Theorem 2.6.3 — Random-$\alpha$ with density $e^\alpha/(e-1)$ has expected ratio at most $e/(e-1)$
-- statement:
--   Consider one-machine scheduling with release dates to minimize weighted completion time: processing times $p_j>0$, release dates $r_j\ge0$, weights $w_j>0$. Let $P$ be a preemptive schedule that is optimal among all preemptive schedules for $\sum_j w_jC_j$. Choose $\alpha\in(0,1]$ with density $f(\alpha)=e^\alpha/(e-1)$ and let $C^\alpha_j$ be the completion time of $J_j$ in the $\alpha$-schedule derived from $P$ (ties broken by job index). Then for every feasible nonpreemptive schedule with completion times $C_j$,
--   $$E\Bigl[\sum_j w_jC^\alpha_j\Bigr]=\int_0^1\frac{e^\alpha}{e-1}\sum_j w_jC^\alpha_j\,d\alpha\le\frac{e}{e-1}\sum_j w_jC_j ,$$
--   and the integrand is integrable. That is, the expected approximation ratio is at most $e/(e-1)\approx1.58$.
--
--   This is the bound from which Corollary 2.7 (Best-$\alpha$) follows.
--
--   **Formalization Note** "Approximation ratio" is stated as the inequality against every feasible nonpreemptive schedule. The optimality of $P$ among preemptive schedules is the paper's standing assumption for its upper bounds (p. 151).
-- source:
--   Chekuri, Motwani, Natarajan, Stein, Approximation Techniques for Average Completion Time Scheduling, SIAM J. Comput. 31(1), 2001, p. 154, Theorem 2.6, part 3 (proof pp. 154–155); standing assumption p. 151

import Mathlib
import Definitions.Def_AvgCompletionSched_BestAlpha_Model

namespace AvgCompletionSched.BestAlpha
theorem random_alpha_exp {n : ℕ} {I : Instance n} (w : Fin n → ℝ) (hw : ∀ j, 0 < w j)
    (P : PreemptiveSchedule I)
    (hP : ∀ P' : PreemptiveSchedule I, ∑ j, w j * P.CP j ≤ ∑ j, w j * P'.CP j)
    (N : NonpreemptiveSchedule I) :
    IntervalIntegrable (fun α => Real.exp α / (Real.exp 1 - 1) * ∑ j, w j * P.Calpha α j)
        MeasureTheory.volume 0 1 ∧
      ∫ α in (0 : ℝ)..1, Real.exp α / (Real.exp 1 - 1) * ∑ j, w j * P.Calpha α j
        ≤ Real.exp 1 / (Real.exp 1 - 1) * ∑ j, w j * N.C j := by sorry
end AvgCompletionSched.BestAlpha
