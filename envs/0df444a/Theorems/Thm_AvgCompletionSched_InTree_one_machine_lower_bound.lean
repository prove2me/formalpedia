-- Prove2me | Theorems.Thm_AvgCompletionSched_InTree_one_machine_lower_bound
-- name    : AvgCompletionSched.InTree.one_machine_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T20:10:13.372096+00:00
-- url     : https://prove2.me/theorems/a8124f4d-0983-4797-8b7e-93d60514506a
-- title:
--   Lemma 4.10 — $C^m_{\mathrm{OPT}} \ge C^1_{\mathrm{OPT}}/m$
-- statement:
--   Let an in-tree instance without release dates and a number $m\ge 1$ of machines be given, and let $\pi$ be an optimal one-machine schedule, with weighted completion time $C^1_{\mathrm{OPT}}=\sum_j w_jC^1_j$. Then every feasible nonpreemptive $m$-machine schedule $N$ satisfies
--   $$\frac{C^1_{\mathrm{OPT}}}{m}\le \sum_j w_j C^N_j .$$
--   In particular $C^m_{\mathrm{OPT}}\ge C^1_{\mathrm{OPT}}/m$.
--
--   Together with Lemma 4.11 this is one of the two lower bounds on the $m$-machine optimum against which the list schedule is compared in Theorem 4.17.
--
--   **Formalization Note** The optimum $C^m_{\mathrm{OPT}}$ is not formed as an infimum; the bound is stated against every feasible schedule. The paper proves the lemma for general precedence constraints and release dates; it is stated here in this mission's model (in-trees, no release dates), where it is used.
-- source:
--   Chekuri, Motwani, Natarajan, Stein, Approximation Techniques for Average Completion Time Scheduling, SIAM J. Comput. 31(1), 2001, p. 160, Lemma 4.10

import Mathlib
import Definitions.Def_AvgCompletionSched_InTree_Model

namespace AvgCompletionSched.InTree

/-- Lemma 4.10 (p. 160): `C^m_opt ≥ C^1_opt / m`. -/
theorem one_machine_lower_bound {n : ℕ} (I : Instance n) (m : ℕ) (hm : 1 ≤ m)
    (π : Fin n ≃ Fin n) (hπ : IsOptimalOneMachine I π) (N : Schedule I m) :
    oneMachineWct I π / (m : ℝ) ≤ N.wct := by sorry

end AvgCompletionSched.InTree
