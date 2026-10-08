-- Prove2me | Theorems.Thm_BurnInBatch_ListSched_proposition_1
-- name    : BurnInBatch.ListSched.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T14:07:13.160111+00:00
-- url     : https://prove2.me/theorems/6828c7fa-4519-4e1d-9bc4-efe9c6816763
-- title:
--   Proposition 1 — BLS makespan bound
-- statement:
--   Let $J$ be any finite set of jobs with positive processing times, let $B>0$ be the batch capacity, and let $m>0$ be the number of identical machines. For **every** ordering of the jobs in $J$, let $C_{\max}^{\mathrm{BLS}}(J)$ be the makespan obtained by grouping successive jobs into batches and assigning the batches to the first available machines. If $C_{\max}^*(J)$ is the minimum over all valid batchings and machine assignments, then
--
--   $$
--   C_{\max}^{\mathrm{BLS}}(J)\le\left(B+1-\frac1m\right)C_{\max}^*(J).
--   $$
--
--   Taking $J$ to be the full job set gives Proposition 1. When $B=1$, the factor becomes Graham's $2-1/m$ list-scheduling bound. The sub-instance form is also used for prefixes in the maximum-lateness analysis.
--
--   **Formalization Note** The list may be any permutation of $J$, including the empty list when $J$ is empty. The published list-scheduling rule resolves simultaneous machine availability by lowest machine index; any such tie has the same makespan. The batch optimum is taken over all valid batchings, not only BLS-style consecutive batches.
-- source:
--   Lee, Uzsoy & Martin-Vega, Efficient Algorithms for Scheduling Semiconductor Burn-In Operations, Oper. Res. 40(4) (1992), p. 772, Proposition 1; https://doi.org/10.1287/opre.40.4.764

import Mathlib
import Definitions.Def_BurnInBatch_ListSched_Model

namespace BurnInBatch.ListSched

/-- Proposition 1, p. 772, also valid for every sub-instance `J`. -/
theorem proposition_1 {n : ℕ} (p : Fin n → ℝ) (B m : ℕ)
    (J : Finset (Fin n)) (l : List (Fin n))
    (hB : 0 < B) (hm : 0 < m) (hp : ∀ j, 0 < p j)
    (hl : ListsJobs J l) :
    blsMakespan p B m l ≤
      ((B : ℝ) + 1 - 1 / (m : ℝ)) * CmaxStar p B m J := by sorry

end BurnInBatch.ListSched
