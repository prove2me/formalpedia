-- Prove2me | Theorems.Thm_BurnInBatch_TardyJobs_dp3_variable_correct
-- name    : BurnInBatch.TardyJobs.dp3_variable_correct
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:39:25.617072+00:00
-- url     : https://prove2.me/theorems/80362206-ed9b-4407-b1b1-aee1657464f6
-- title:
--   §4 — variable-time extension of DP3 minimizes tardy jobs
-- statement:
--   All jobs are available at time zero on one batch machine of capacity $B\ge1$. Their processing times $p_j$ and due dates $d_j$ are both nondecreasing in job index. Let $g(i,j)$ be the variable-time DP3 table using $g(i-k,j-k)+p_j$ for a final on-time batch of $k$ jobs when the result does not exceed $d_{j-k+1}$. If $U^*$ is the minimum number of tardy jobs over complete valid batch schedules, then
--
--   $$
--   U^*=n-\max\{0\le i\le n:g(i,n)<+\infty\}.
--   $$
--
--   This extends the algorithmic characterization to agreeable unequal processing times.
--
--   **Formalization Note** The paper prints a final range starting at one; zero is included to make the all-tardy case defined. Jobs are indexed so both $p$ and $d$ are nondecreasing. The stated $O(n^2B)$ running-time bound is not formalized.
-- source:
--   Lee, Uzsoy & Martin-Vega, Efficient Algorithms for Scheduling Semiconductor Burn-In Operations, Oper. Res. 40(4) (1992), p. 771, §4, extension of DP3 to 1/B/Σ U_i

import Mathlib
import Definitions.Def_BurnInBatch_TardyJobs_Model
import Definitions.Def_BurnInBatch_TardyJobs_DP3Variable

namespace BurnInBatch.TardyJobs

/-- The §4 extension of DP3, p. 771, to agreeable processing times and due dates. -/
theorem dp3_variable_correct {n : ℕ} (B : ℕ) (p d : Fin n → ℕ)
    (hB : 0 < B) (hd : Monotone d) (hp : Monotone p) :
    n - dp3VariableMaxOnTime B p d = minTardy B p (fun _ => 0) d := by sorry

end BurnInBatch.TardyJobs
