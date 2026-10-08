-- Prove2me | Theorems.Thm_AvgCompletionSched_BestAlpha_alpha_schedule_completion_bound
-- name    : AvgCompletionSched.BestAlpha.alpha_schedule_completion_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T19:48:20.475984+00:00
-- url     : https://prove2.me/theorems/a581378e-b90b-4209-9196-c59b04f88847
-- title:
--   Lemma 2.3 — $C^\alpha_i \le T_i + (1+\alpha)\sum_{\beta\ge\alpha}S^P_i(\beta)+\sum_{\beta<\alpha}\beta S^P_i(\beta)$
-- statement:
--   Let $P$ be any preemptive one-machine schedule of an instance with processing times $p_j>0$ and release dates $r_j\ge0$, and let $\alpha\in(0,1]$. Let $\pi$ be any ordering of the jobs in nondecreasing order of their $\alpha$-points $C^P_j(\alpha)$, with ties in any order, and let $C^\alpha_i$ be the completion time of job $J_i$ when the jobs are list-scheduled nonpreemptively in the order $\pi$. With $T_i$ the idle time of $P$ before $C^P_i$ and $x_{ij}$ the fraction of $J_j$ processed before $C^P_i$,
--   $$C^\alpha_i\le T_i+(1+\alpha)\sum_{j:\,x_{ij}\ge\alpha}p_j+\sum_{j:\,x_{ij}<\alpha}x_{ij}\,p_j .$$
--   In the paper's notation this is $C^\alpha_i\le T_i+(1+\alpha)\sum_{\beta\ge\alpha}S^P_i(\beta)+\sum_{\beta<\alpha}\beta S^P_i(\beta)$.
--
--   This is the key structural bound of the mission: jobs that are at least an $\alpha$-fraction done by $C^P_i$ may be charged up to $1+\alpha$ times their length, the others only their processed part. Averaging it over a random $\alpha$ gives Lemma 2.5.
--
--   **Formalization Note** The bound is stated for every tie-breaking among equal $\alpha$-points. The sums over $\beta$ are reindexed as sums over jobs.
-- source:
--   Chekuri, Motwani, Natarajan, Stein, Approximation Techniques for Average Completion Time Scheduling, SIAM J. Comput. 31(1), 2001, p. 151, Lemma 2.3 (proof pp. 151–153)

import Mathlib
import Definitions.Def_AvgCompletionSched_BestAlpha_Model

namespace AvgCompletionSched.BestAlpha
theorem alpha_schedule_completion_bound {n : ℕ} {I : Instance n}
    (P : PreemptiveSchedule I) (α : ℝ) (hα : α ∈ Set.Ioc (0 : ℝ) 1)
    (π : Fin n ≃ Fin n) (hπ : IsAlphaOrder P α π) (i : Fin n) :
    listCompletion I π i ≤
      P.idle i + (1 + α) * ∑ j ∈ Finset.univ.filter (fun j => α ≤ P.frac i j), I.p j
        + ∑ j ∈ Finset.univ.filter (fun j => P.frac i j < α), P.frac i j * I.p j := by sorry
end AvgCompletionSched.BestAlpha
