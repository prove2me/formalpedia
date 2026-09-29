-- Prove2me | Theorems.Thm_AvgCompletionSched_DelayList_one_machine_lower_bound
-- name    : AvgCompletionSched.DelayList.one_machine_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T20:05:39.992373+00:00
-- url     : https://prove2.me/theorems/fedef03c-18ad-4fbe-9647-efbd76243147
-- title:
--   Lemma 4.10 — $C^m_{\mathrm{OPT}} \ge C^1_{\mathrm{OPT}}/m$
-- statement:
--   Let an instance with release dates, positive weights and precedence constraints be given, and let $m$ be a number of machines. For every feasible nonpreemptive $m$-machine schedule $S^m$ there is a feasible one-machine schedule $S^1$ of the same instance (respecting the same release dates and precedence constraints) with
--   $$\sum_j w_jC^1_j\le m\sum_j w_jC^m_j .$$
--
--   In particular the optimal $m$-machine value is at least $1/m$ times the optimal one-machine value, $C^m_{\mathrm{OPT}}\ge C^1_{\mathrm{OPT}}/m$; this is how Theorem 4.13 compares the one-machine schedule it starts from with the $m$-machine optimum.
--
--   **Formalization Note** The optimum is not formed as an infimum; the statement is quantified over every $m$-machine schedule. The paper states the lemma for preemptive or nonpreemptive one-machine schedules; the nonpreemptive one-machine schedule is formalized, which is the stronger claim since nonpreemptive schedules are special preemptive ones.
-- source:
--   Chekuri, Motwani, Natarajan, Stein, Approximation Techniques for Average Completion Time Scheduling, SIAM J. Comput. 31(1), 2001, p. 160, Lemma 4.10

import Mathlib
import Definitions.Def_AvgCompletionSched_DelayList_Model

namespace AvgCompletionSched.DelayList

/-- Lemma 4.10 (p. 160): `C^m_opt ≥ C^1_opt / m`. For every feasible `m`-machine schedule `N`
there is a feasible one-machine schedule of the same instance (same release dates and precedence
constraints) whose sum of weighted completion times is at most `m` times that of `N`. -/
theorem one_machine_lower_bound {n m : ℕ} (I : Instance n) (N : Schedule I m) :
    ∃ S1 : Schedule I 1, S1.wct ≤ (m : ℝ) * N.wct := by sorry

end AvgCompletionSched.DelayList
