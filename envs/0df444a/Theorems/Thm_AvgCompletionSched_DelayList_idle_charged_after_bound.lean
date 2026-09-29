-- Prove2me | Theorems.Thm_AvgCompletionSched_DelayList_idle_charged_after_bound
-- name    : AvgCompletionSched.DelayList.idle_charged_after_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T20:04:34.926765+00:00
-- url     : https://prove2.me/theorems/fcae5c05-07cb-48ff-8b1b-9f02240d13dd
-- title:
--   Lemma 4.8 — idle time charged to $A_i$ before $s^m_i$ is at most $m(\kappa'_i - p_i)$, so $p(O_i) \le m(\kappa'_i - p_i)/\beta$
-- statement:
--   Let $S^m$ be a schedule produced by the continuous-time algorithm Delay List with parameter $\beta>0$ on $m\ge 2$ machines, using a list that obeys the precedence constraints. For every job $J_i$ and every path $P'_i$ of Definition 4.4, with length $\kappa'_i$:
--
--   1. the total idle time charged to jobs in $A_i$, lying in the interval $(0,s^m_i)$, is at most $m(\kappa'_i-p_i)$;
--   2. consequently
--   $$p(O_i)\le\frac{m(\kappa'_i-p_i)}{\beta}\le\frac{m(\kappa_i-p_i)}{\beta}.$$
--
--   The lemma bounds how much work from later in the list the algorithm can run before $J_i$.
-- source:
--   Chekuri, Motwani, Natarajan, Stein, Approximation Techniques for Average Completion Time Scheduling, SIAM J. Comput. 31(1), 2001, pp. 159–160, Lemma 4.8

import Mathlib
import Definitions.Def_AvgCompletionSched_DelayList_Model
import Definitions.Def_AvgCompletionSched_DelayList_Algorithm
import Definitions.Def_AvgCompletionSched_DelayList_Analysis

namespace AvgCompletionSched.DelayList

/-- Lemma 4.8 (pp. 159–160): for every job `J_i` and every path `P′_i` of Definition 4.4, the
total idle time charged to jobs in `A_i`, in the interval `(0, s^m_i)`, is at most
`m (κ′_i − p_i)`; consequently `p(O_i) ≤ m (κ′_i − p_i)/β ≤ m (κ_i − p_i)/β`. -/
theorem idle_charged_after_bound {n m : ℕ} (I : Instance n) (hm : 2 ≤ m) (π : Fin n ≃ Fin n)
    (hπ : ObeysPrecedence I π) (β : ℝ) (hβ : 0 < β) (D : DelayListRun I m)
    (hD : IsDelayListSchedule I m π β D) (i j₁ : Fin n) (l : List (Fin n))
    (hP : D.IsPathPrime i j₁ l) :
    D.chargedToIn (listA π i) (Set.Ioo 0 (D.S i)) ≤ (m : ℝ) * (kappaPrime I j₁ l - I.p i) ∧
    psum I (D.outOfOrder π i) ≤ (m : ℝ) * (kappaPrime I j₁ l - I.p i) / β ∧
    (m : ℝ) * (kappaPrime I j₁ l - I.p i) / β ≤ (m : ℝ) * (kappa I i - I.p i) / β := by sorry

end AvgCompletionSched.DelayList
