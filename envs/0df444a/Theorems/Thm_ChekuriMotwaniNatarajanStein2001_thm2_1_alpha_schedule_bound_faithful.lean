-- Prove2me | Theorems.Thm_ChekuriMotwaniNatarajanStein2001_thm2_1_alpha_schedule_bound_faithful
-- name    : ChekuriMotwaniNatarajanStein2001.thm2_1_alpha_schedule_bound_faithful
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-23T01:29:20.387331+00:00
-- url     : https://prove2.me/theorems/f0b4de50-8b0e-4ee6-9494-bfb51537d812
-- title:
--   Theorem 2.1 — an $\alpha$-schedule is within $1 + 1/\alpha$ of its preemptive schedule
-- statement:
--   Consider one-machine scheduling of $n$ jobs with processing times $p_j>0$ and release dates $r_j\ge0$. Let $P$ be any preemptive one-machine schedule, with completion times $C^P_j$ and $\alpha$-points $C^P_j(\alpha)$ (the time at which $\alpha p_j$ units of $J_j$ have been processed). Fix $\alpha\in(0,1]$ and list-schedule the jobs nonpreemptively in any nondecreasing order of $C^P_j(\alpha)$, each job starting at the later of its release date and the completion of the previous job. The resulting $\alpha$-schedule satisfies
--
--   $$\sum_j C^\alpha_j\le\Bigl(1+\frac1\alpha\Bigr)\sum_j C^P_j .$$
--
--   This is the upper-bound part of Theorem 2.1 of Chekuri, Motwani, Natarajan and Stein, the basic deterministic $\alpha$-point bound that the randomized analysis of Lemma 2.5 and Theorem 2.6 improves; for $\alpha=1$ it gives the classical factor $2$. It holds for every preemptive schedule $P$, optimal or not.
--
--   **Formalization Note** The tightness part of the theorem uses zero-length jobs, which the instance type (with $p_j>0$) excludes; it is not included. Ties between equal $\alpha$-points may be broken in any way.
-- source:
--   Chekuri, Motwani, Natarajan, Stein, Approximation Techniques for Average Completion Time Scheduling, SIAM J. Comput. 31(1) (2001), doi:10.1137/S0097539797327180, p. 150, Theorem 2.1 (α-schedules defined p. 148)

import Mathlib
import Definitions.Def_AvgCompletionSched_BestAlpha_Model

open AvgCompletionSched.BestAlpha

theorem ChekuriMotwaniNatarajanStein2001.thm2_1_alpha_schedule_bound_faithful {n : ℕ} {I : Instance n}
    (P : PreemptiveSchedule I) (α : ℝ) (hα : α ∈ Set.Ioc (0 : ℝ) 1)
    (π : Fin n ≃ Fin n) (hπ : IsAlphaOrder P α π) :
    ∑ j, listCompletion I π j ≤ (1 + 1 / α) * ∑ j, P.CP j := by sorry
