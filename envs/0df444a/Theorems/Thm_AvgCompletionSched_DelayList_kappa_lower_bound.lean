-- Prove2me | Theorems.Thm_AvgCompletionSched_DelayList_kappa_lower_bound
-- name    : AvgCompletionSched.DelayList.kappa_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T20:06:11.486295+00:00
-- url     : https://prove2.me/theorems/d599fb0e-8c7e-4cd4-9e4f-0365ad23b6a9
-- title:
--   Lemma 4.11 — $C^m_{\mathrm{OPT}} \ge \sum_i w_i\kappa_i = C^\infty_{\mathrm{OPT}}$
-- statement:
--   Let an instance with release dates, positive weights and precedence constraints be given, and let $m$ be a number of machines. Then
--
--   1. every feasible $m$-machine schedule $S^m$ satisfies
--   $$\sum_i w_i\kappa_i\le\sum_i w_iC^m_i ;$$
--   2. with unboundedly many machines the bound is attained: there is a feasible schedule on $n$ machines (one per job) whose sum of weighted completion times equals $\sum_i w_i\kappa_i$.
--
--   Together, since part 1 holds for every number of machines, $\sum_i w_i\kappa_i=C^\infty_{\mathrm{OPT}}$ is the optimum with unboundedly many machines and a lower bound on $C^m_{\mathrm{OPT}}$.
--
--   **Formalization Note** "Unboundedly many machines" is modelled by $n$ machines, which suffice because a schedule never runs more than $n$ jobs at a time.
-- source:
--   Chekuri, Motwani, Natarajan, Stein, Approximation Techniques for Average Completion Time Scheduling, SIAM J. Comput. 31(1), 2001, p. 160, Lemma 4.11

import Mathlib
import Definitions.Def_AvgCompletionSched_DelayList_Model

namespace AvgCompletionSched.DelayList

/-- Lemma 4.11 (p. 160): `C^m_opt ≥ ∑_i w_i κ_i = C^∞_opt`. Every feasible `m`-machine schedule
has sum of weighted completion times at least `∑_i w_i κ_i`, and with unboundedly many machines
(`n` machines suffice) there is a feasible schedule whose sum of weighted completion times equals
`∑_i w_i κ_i`. -/
theorem kappa_lower_bound {n m : ℕ} (I : Instance n) :
    (∀ N : Schedule I m, ∑ i, I.w i * kappa I i ≤ N.wct) ∧
    ∃ N : Schedule I n, N.wct = ∑ i, I.w i * kappa I i := by sorry

end AvgCompletionSched.DelayList
