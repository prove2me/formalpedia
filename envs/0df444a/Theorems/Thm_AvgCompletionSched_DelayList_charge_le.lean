-- Prove2me | Theorems.Thm_AvgCompletionSched_DelayList_charge_le
-- name    : AvgCompletionSched.DelayList.charge_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T20:03:12.718081+00:00
-- url     : https://prove2.me/theorems/a6d9e570-a6ce-4e4d-8083-ba7f2dbb967d
-- title:
--   Fact 4.6 — the idle time charged to each job $J_i$ is at most $\beta p_i$
-- statement:
--   Let $S^m$ be a schedule produced by the continuous-time algorithm Delay List with parameter $\beta>0$ on $m\ge 2$ machines, using a list that obeys the precedence constraints. For every job $J_i$, the idle time charged to $J_i$ satisfies
--   $$\text{(idle time charged to } J_i)\le\beta p_i .$$
--
--   For a job scheduled out of order (case 2) the charge is exactly $\beta p_i$ by the rules of the algorithm; the content is the in-order case 1, where $J_i$ is charged all uncharged idle time in $(q^m_i,s^m_i)$.
--
--   **Formalization Note** This is the statement for which the continuous-time version of the algorithm is formalized: the paper remarks that with discrete time units the algorithm "might charge more idle time due to integrality of the time unit", and that this is fixed in the continuous case.
-- source:
--   Chekuri, Motwani, Natarajan, Stein, Approximation Techniques for Average Completion Time Scheduling, SIAM J. Comput. 31(1), 2001, p. 159, Fact 4.6 (and its proof)

import Mathlib
import Definitions.Def_AvgCompletionSched_DelayList_Model
import Definitions.Def_AvgCompletionSched_DelayList_Algorithm

namespace AvgCompletionSched.DelayList

/-- Fact 4.6 (p. 159): in the continuous-time Delay List algorithm, the idle time charged to each
job `J_i` is at most `β p_i`. -/
theorem charge_le {n m : ℕ} (I : Instance n) (hm : 2 ≤ m) (π : Fin n ≃ Fin n)
    (hπ : ObeysPrecedence I π) (β : ℝ) (hβ : 0 < β) (D : DelayListRun I m)
    (hD : IsDelayListSchedule I m π β D) (i : Fin n) :
    D.charge i ≤ β * I.p i := by sorry

end AvgCompletionSched.DelayList
