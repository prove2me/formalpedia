-- Prove2me | Theorems.Thm_ChekuriMotwaniNatarajanStein2001_cor2_4_alpha_schedule_makespan_faithful
-- name    : ChekuriMotwaniNatarajanStein2001.cor2_4_alpha_schedule_makespan_faithful
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-23T01:29:28.573276+00:00
-- url     : https://prove2.me/theorems/1af91c41-4f7e-4453-9b3f-c8a11d948d58
-- title:
--   Corollary 2.4 — makespan of an $\alpha$-schedule (upper bound)
-- statement:
--   Consider one-machine scheduling of $n$ jobs with processing times $p_j>0$ and release dates $r_j\ge0$. Let $P$ be a preemptive one-machine schedule with completion times $C^P_j$, let $\alpha\in(0,1]$, and let $C^\alpha_{\max}$ be the makespan of an $\alpha$-schedule derived from $P$ (list scheduling in any nondecreasing order of the $\alpha$-points $C^P_j(\alpha)$). Then
--
--   $$C^\alpha_{\max}\le(1+\alpha)\max_j C^P_j .$$
--
--   This is the upper-bound part of Corollary 2.4 of Chekuri, Motwani, Natarajan and Stein: $\alpha$-schedules lose at most a factor $1+\alpha$ in makespan.
--
--   **Formalization Note** The preemptive makespan is passed as any $T\ge0$ with $C^P_j\le T$ for all $j$ (equivalent to $T=\max_j C^P_j$ when $n\ge1$, and harmless when $n=0$). The makespan of the $\alpha$-schedule is the finishing time of the whole list. The tightness part, which needs specific instances, is not included.
-- source:
--   Chekuri, Motwani, Natarajan, Stein, Approximation Techniques for Average Completion Time Scheduling, SIAM J. Comput. 31(1) (2001), doi:10.1137/S0097539797327180, p. 153, Corollary 2.4

import Mathlib
import Definitions.Def_AvgCompletionSched_BestAlpha_Model

open AvgCompletionSched.BestAlpha

theorem ChekuriMotwaniNatarajanStein2001.cor2_4_alpha_schedule_makespan_faithful {n : ℕ}
    {I : Instance n} (P : PreemptiveSchedule I) (α : ℝ) (hα : α ∈ Set.Ioc (0 : ℝ) 1)
    (π : Fin n ≃ Fin n) (hπ : IsAlphaOrder P α π) (T : ℝ) (hT0 : 0 ≤ T)
    (hT : ∀ j, P.CP j ≤ T) :
    listFinish I π n ≤ (1 + α) * T := by sorry
