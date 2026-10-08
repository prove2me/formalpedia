-- Prove2me | Theorems.Thm_AvgCompletionSched_BestAlpha_best_alpha_approximation
-- name    : AvgCompletionSched.BestAlpha.best_alpha_approximation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T19:51:32.329908+00:00
-- url     : https://prove2.me/theorems/ffd82add-3f89-47f5-bca6-76403033fde0
-- title:
--   Corollary 2.7 — Best-$\alpha$ is an $e/(e-1)$-approximation for $1|r_j|\sum C_j$
-- statement:
--   Consider nonpreemptive scheduling on one machine with release dates to minimize total (equivalently, average) completion time: processing times $p_j>0$ and release dates $r_j\ge0$. Let $P$ be a preemptive schedule that is optimal among all preemptive schedules for $\sum_jC_j$ (for example the SRPT schedule). Then there is an $\alpha\in(0,1]$ such that every $\alpha$-schedule derived from $P$ (list scheduling in any nondecreasing order of the $\alpha$-points $C^P_j(\alpha)$) satisfies, for every feasible nonpreemptive schedule with completion times $C_j$,
--   $$\sum_j C^\alpha_j\le\frac{e}{e-1}\sum_j C_j .$$
--
--   Algorithm Best-$\alpha$ outputs the $\alpha$-schedule of smallest total completion time, whose value is at most that of this $\alpha$; hence Best-$\alpha$ is an $e/(e-1)$-approximation algorithm ($e/(e-1)\approx1.58$).
--
--   **Formalization Note** The existential form over $\alpha$ replaces the minimum over $\alpha$ taken by Best-$\alpha$; $\alpha$ is chosen before the comparison schedule, so a single $\alpha$ works against every feasible nonpreemptive schedule. The running-time claim $O(n^2)$ is not formalized. The optimality of $P$ among preemptive schedules is the paper's standing assumption for its upper bounds (p. 151); the paper obtains $P$ from SRPT.
-- source:
--   Chekuri, Motwani, Natarajan, Stein, Approximation Techniques for Average Completion Time Scheduling, SIAM J. Comput. 31(1), 2001, p. 155, Corollary 2.7; Best-α defined p. 155; standing assumption p. 151

import Mathlib
import Definitions.Def_AvgCompletionSched_BestAlpha_Model

namespace AvgCompletionSched.BestAlpha
theorem best_alpha_approximation {n : ℕ} {I : Instance n} (P : PreemptiveSchedule I)
    (hP : ∀ P' : PreemptiveSchedule I, ∑ j, P.CP j ≤ ∑ j, P'.CP j) :
    ∃ α ∈ Set.Ioc (0 : ℝ) 1, ∀ π : Fin n ≃ Fin n, IsAlphaOrder P α π →
      ∀ N : NonpreemptiveSchedule I,
        ∑ j, listCompletion I π j ≤ Real.exp 1 / (Real.exp 1 - 1) * ∑ j, N.C j := by sorry
end AvgCompletionSched.BestAlpha
