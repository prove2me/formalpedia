-- Prove2me | Theorems.Thm_AvgCompletionSched_InTree_kappa_lower_bound
-- name    : AvgCompletionSched.InTree.kappa_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T20:11:00.513735+00:00
-- url     : https://prove2.me/theorems/9c5c20d0-ff5b-4bfe-84a4-fceb87602e8e
-- title:
--   Lemma 4.11 — $C^m_{\mathrm{OPT}} \ge \sum_i w_i\kappa_i = C^\infty_{\mathrm{OPT}}$
-- statement:
--   Let an in-tree instance without release dates be given, and let $\kappa_i$ be the critical-path length of job $i$ (Definition 4.1). Then:
--
--   1. for every number $m$ of machines, every feasible nonpreemptive $m$-machine schedule $N$ satisfies
--   $$\sum_i w_i\kappa_i\le \sum_i w_i C^N_i ,$$
--   so $C^m_{\mathrm{OPT}}\ge\sum_i w_i\kappa_i$;
--   2. with unboundedly many machines the value $\sum_i w_i\kappa_i$ is attained: some feasible schedule on $n$ machines (as many machines as jobs, which is as good as unboundedly many) has $\sum_i w_i C^N_i=\sum_i w_i\kappa_i$. Together with part 1 this is the equality $\sum_i w_i\kappa_i=C^\infty_{\mathrm{OPT}}$.
--
--   Part 1 is the second lower bound used in Theorem 4.17.
--
--   **Formalization Note** The optimum is not formed as an infimum: part 1 is stated against every feasible schedule, and $C^\infty_{\mathrm{OPT}}$ is rendered as "attained on $n$ machines" (no schedule on any number of machines does better, by part 1).
-- source:
--   Chekuri, Motwani, Natarajan, Stein, Approximation Techniques for Average Completion Time Scheduling, SIAM J. Comput. 31(1), 2001, p. 160, Lemma 4.11

import Mathlib
import Definitions.Def_AvgCompletionSched_InTree_Model

namespace AvgCompletionSched.InTree

/-- Lemma 4.11 (p. 160): `C^m_opt ≥ ∑_i w_i κ_i = C^∞_opt`. First part: every feasible schedule
on any number `m` of machines has value at least `∑_i w_i κ_i`. Second part (the equality with
`C^∞_opt`): with unboundedly many machines (`n` machines suffice for `n` jobs) the value
`∑_i w_i κ_i` is attained, so together with the first part it is the optimum. -/
theorem kappa_lower_bound {n : ℕ} (I : Instance n) :
    (∀ (m : ℕ) (N : Schedule I m), ∑ i, I.w i * kappa I i ≤ N.wct) ∧
    ∃ N : Schedule I n, N.wct = ∑ i, I.w i * kappa I i := by sorry

end AvgCompletionSched.InTree
