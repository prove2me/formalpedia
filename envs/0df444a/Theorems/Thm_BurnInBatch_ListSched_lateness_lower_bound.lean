-- Prove2me | Theorems.Thm_BurnInBatch_ListSched_lateness_lower_bound
-- name    : BurnInBatch.ListSched.lateness_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T14:08:01.237631+00:00
-- url     : https://prove2.me/theorems/62baecde-8a7f-4392-83a0-4c1d7f0e5e6e
-- title:
--   Proof of Proposition 4 — sub-instance lateness lower bound
-- statement:
--   Let $J$ be a nonempty subset of the jobs, with positive processing times, batch capacity $B>0$, and $m>0$ parallel machines. Let $L^*(J)$ be the least maximum lateness achievable for $J$, let $C_{\max}^*(J)$ be its least makespan, and let $d_{\max}$ be the greatest due date among **all** jobs. Then
--
--   $$
--   L^*(J)\ge C_{\max}^*(J)-d_{\max}.
--   $$
--
--   The estimate connects a lateness optimum on the prefix sub-instance with the makespan bound of Proposition 1.
--
--   **Formalization Note** The full instance has at least one job so its maximum due date is defined. This item needs no sign condition on due dates; the goal theorem separately assumes nonnegative due dates.
-- source:
--   Lee, Uzsoy & Martin-Vega, Efficient Algorithms for Scheduling Semiconductor Burn-In Operations, Oper. Res. 40(4) (1992), p. 773, proof of Proposition 4, display “L*(S_k) ≥ C_max*(S_k) − d_max”; https://doi.org/10.1287/opre.40.4.764

import Mathlib
import Definitions.Def_BurnInBatch_ListSched_Model

namespace BurnInBatch.ListSched

/-- Proof of Proposition 4, p. 773: the lateness optimum on a sub-instance
is at least its makespan optimum minus the full instance's largest due date. -/
theorem lateness_lower_bound {n : ℕ} (p d : Fin n → ℝ) (B m : ℕ)
    (J : Finset (Fin n)) (hn : 0 < n) (hJ : J.Nonempty)
    (hB : 0 < B) (hm : 0 < m) (hp : ∀ j, 0 < p j) :
    CmaxStar p B m J - maxDue d hn ≤ LStar p d B m J := by sorry

end BurnInBatch.ListSched
