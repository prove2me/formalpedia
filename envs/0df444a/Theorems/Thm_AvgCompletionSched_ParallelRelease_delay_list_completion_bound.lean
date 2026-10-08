-- Prove2me | Theorems.Thm_AvgCompletionSched_ParallelRelease_delay_list_completion_bound
-- name    : AvgCompletionSched.ParallelRelease.delay_list_completion_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T19:57:08.152801+00:00
-- url     : https://prove2.me/theorems/a514badf-318e-4704-83a2-eb23d4c8e68c
-- title:
--   Theorem 4.9 (no precedence) — $C_i\le(1+\beta)p(B_i)/m+(1+1/\beta)(r_i+p_i)-p_i/\beta$
-- statement:
--   Let $m\ge2$, let $\beta>0$, let $\pi$ be a list of the jobs, and let $D$ be a schedule produced by the continuous-time Delay List algorithm with parameter $\beta$ on the list $\pi$, for jobs with release dates and no precedence constraints. For a job $J_i$ let $B_i$ be the set of jobs at or before $J_i$ in the list (including $J_i$) and $p(B_i)=\sum_{k\in B_i}p_k$. Then every job satisfies
--   $$C^D_i\le\frac{(1+\beta)\,p(B_i)}{m}+\Bigl(1+\frac1\beta\Bigr)(r_i+p_i)-\frac{p_i}{\beta}.$$
--
--   This is Theorem 4.9 specialised to an instance without precedence constraints. There, the critical-path quantity $\kappa_i$ of Definition 4.1 is $r_i+p_i$, and the path $P'_i$ of Definition 4.4 consists of $J_i$ alone, so $\kappa'_i=\kappa_i=r_i+p_i$ (Fact 4.5 holds with equality). The theorem is the per-job guarantee from which Lemma 4.18 follows by summation.
--
--   **Formalization Note** Delay List is the continuous-time version of §4.1, with case-2 charges taken from the most recent uncharged idle time (see the definition file). The hypothesis $m\ge2$ is the setting of §4.1 ("a schedule for $m\ge2$ machines").
-- source:
--   Chekuri, Motwani, Natarajan, Stein, Approximation Techniques for Average Completion Time Scheduling, SIAM J. Comput. 31(1), 2001, p. 160, Theorem 4.9 (with Definitions 4.1, 4.3, 4.4 and Fact 4.5, pp. 158–159)

import Mathlib
import Definitions.Def_AvgCompletionSched_ParallelRelease_Model
import Definitions.Def_AvgCompletionSched_ParallelRelease_DelayList

namespace AvgCompletionSched.ParallelRelease

/-- Theorem 4.9 without precedence constraints (`κ_i = r_i + p_i`): in a Delay List schedule with
parameter `β > 0` on the list `π`, every job satisfies
`C_i ≤ (1 + β) p(B_i)/m + (1 + 1/β)(r_i + p_i) - p_i/β`, where `B_i` is the set of jobs at or
before `i` in the list. -/
theorem delay_list_completion_bound {n m : ℕ} (I : Instance n m) (hm : 2 ≤ m)
    (π : Fin n ≃ Fin n) (β : ℝ) (hβ : 0 < β) (D : DelayListRun I)
    (hD : IsDelayListSchedule I π β D) (i : Fin n) :
    D.C i ≤ (1 + β) * (∑ k ∈ Finset.univ.filter (fun k => π.symm k ≤ π.symm i), I.p k) / m
      + (1 + 1 / β) * (I.r i + I.p i) - I.p i / β := by sorry

end AvgCompletionSched.ParallelRelease
