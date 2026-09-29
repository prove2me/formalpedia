-- Prove2me | Theorems.Thm_AvgCompletionSched_DelayList_no_uncharged_idle
-- name    : AvgCompletionSched.DelayList.no_uncharged_idle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T20:03:51.290564+00:00
-- url     : https://prove2.me/theorems/ea1f261a-a8d9-413b-86b8-8eca5719da70
-- title:
--   Lemma 4.7 — no uncharged idle time in $(q^m_i, s^m_i)$, and it is charged only to jobs in $B_i$
-- statement:
--   Let $S^m$ be a schedule produced by the continuous-time algorithm Delay List with parameter $\beta>0$ on $m\ge 2$ machines, using a list that obeys the precedence constraints. For every job $J_i$:
--
--   1. once $J_i$ has been scheduled and charged, there is no uncharged idle time in the time interval $(q^m_i,s^m_i)$;
--   2. all the idle time in $(q^m_i,s^m_i)$ is charged only to jobs in $B_i$: for every job $J_k\in A_i$, the idle time in $(q^m_i,s^m_i)$ charged to $J_k$ is $0$.
--
--   In formulas, with $I(t)$ the number of idle machines at time $t$ and $W_k$ the charge window of job $k$,
--   $$\int_{(q^m_i,s^m_i)\setminus\bigcup_{k\ \text{scheduled no later than}\ i}W_k} I(t)\,dt=0 .$$
--
--   The lemma says that between the moment $J_i$ is ready and the moment it starts, idle machines are paid for by $J_i$ and the jobs ahead of it in the list only.
--
--   **Formalization Note** The paper's "all the idle time is charged only to jobs in $B_i$" is read as all the idle time in $(q^m_i,s^m_i)$, which is how its proof uses it.
-- source:
--   Chekuri, Motwani, Natarajan, Stein, Approximation Techniques for Average Completion Time Scheduling, SIAM J. Comput. 31(1), 2001, p. 159, Lemma 4.7

import Mathlib
import Definitions.Def_AvgCompletionSched_DelayList_Model
import Definitions.Def_AvgCompletionSched_DelayList_Algorithm
import Definitions.Def_AvgCompletionSched_DelayList_Analysis

namespace AvgCompletionSched.DelayList

open MeasureTheory

/-- Lemma 4.7 (p. 159): for every job `J_i`, once `J_i` has been scheduled and charged there is
no uncharged idle time in the interval `(q^m_i, s^m_i)`, and all the idle time in that interval
is charged only to jobs in `B_i` (no job of `A_i` is charged idle time lying in it). -/
theorem no_uncharged_idle {n m : ℕ} (I : Instance n) (hm : 2 ≤ m) (π : Fin n ≃ Fin n)
    (hπ : ObeysPrecedence I π) (β : ℝ) (hβ : 0 < β) (D : DelayListRun I m)
    (hD : IsDelayListSchedule I m π β D) (i : Fin n) :
    (∫ t in Set.Ioo (D.q i) (D.S i) \ ⋃ k ∈ {k | D.Before k i ∨ k = i}, D.window k,
        D.idle t) = 0 ∧
    ∀ k ∈ listA π i, (∫ t in D.chargedSet k ∩ Set.Ioo (D.q i) (D.S i), D.idle t) = 0 := by sorry

end AvgCompletionSched.DelayList
