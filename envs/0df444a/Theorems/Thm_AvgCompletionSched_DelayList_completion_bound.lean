-- Prove2me | Theorems.Thm_AvgCompletionSched_DelayList_completion_bound
-- name    : AvgCompletionSched.DelayList.completion_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T20:05:04.347959+00:00
-- url     : https://prove2.me/theorems/35373930-c7e8-4736-ae69-d2809b7ea828
-- title:
--   Theorem 4.9 — $C^m_i \le (1+\beta)p(B_i)/m + (1+1/\beta)\kappa'_i - p_i/\beta$
-- statement:
--   Let $S^m$ be a schedule produced by the continuous-time algorithm Delay List with parameter $\beta>0$ on $m\ge 2$ machines, using a list $\pi$ that obeys the precedence constraints. Then for each job $J_i$ and every path $P'_i$ of Definition 4.4, with length $\kappa'_i$,
--   $$C^m_i\le\frac{(1+\beta)\,p(B_i)}{m}+\Bigl(1+\frac1\beta\Bigr)\kappa'_i-\frac{p_i}{\beta},$$
--   where $B_i$ is the set of jobs up to and including $J_i$ in the list.
--
--   This per-job bound is the core of the conversion: with Fact 4.5 it gives Corollary 4.12 and then Theorem 4.13.
--
--   **Formalization Note** The list is any list obeying the precedence constraints (footnote 2 of the paper), not necessarily the completion order of a schedule.
-- source:
--   Chekuri, Motwani, Natarajan, Stein, Approximation Techniques for Average Completion Time Scheduling, SIAM J. Comput. 31(1), 2001, p. 160, Theorem 4.9

import Mathlib
import Definitions.Def_AvgCompletionSched_DelayList_Model
import Definitions.Def_AvgCompletionSched_DelayList_Algorithm
import Definitions.Def_AvgCompletionSched_DelayList_Analysis

namespace AvgCompletionSched.DelayList

/-- Theorem 4.9 (p. 160): let `S^m` be a schedule produced by the continuous-time algorithm Delay
List using a list `π` that obeys the precedence constraints. Then for each job `J_i` and every
path `P′_i` of Definition 4.4,
`C^m_i ≤ (1 + β) p(B_i)/m + (1 + 1/β) κ′_i − p_i/β`. -/
theorem completion_bound {n m : ℕ} (I : Instance n) (hm : 2 ≤ m) (π : Fin n ≃ Fin n)
    (hπ : ObeysPrecedence I π) (β : ℝ) (hβ : 0 < β) (D : DelayListRun I m)
    (hD : IsDelayListSchedule I m π β D) (i j₁ : Fin n) (l : List (Fin n))
    (hP : D.IsPathPrime i j₁ l) :
    D.C i ≤ (1 + β) * psum I (listB π i) / m + (1 + 1 / β) * kappaPrime I j₁ l
      - I.p i / β := by sorry

end AvgCompletionSched.DelayList
