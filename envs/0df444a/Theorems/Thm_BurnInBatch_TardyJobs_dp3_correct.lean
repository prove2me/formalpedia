-- Prove2me | Theorems.Thm_BurnInBatch_TardyJobs_dp3_correct
-- name    : BurnInBatch.TardyJobs.dp3_correct
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:39:30.84805+00:00
-- url     : https://prove2.me/theorems/c6d4f792-a9b6-4e40-b15a-6bd53eb0b8e2
-- title:
--   §4, Algorithm DP3 — optimal number of tardy jobs
-- statement:
--   On one batch machine with capacity $B\ge1$, let all jobs have common processing time $p$. Index the jobs so that their releases $r_j$ and due dates $d_j$ are nondecreasing. Let $f(i,j)$ be Algorithm DP3's table: $f(0,j)=0$, $f(i,j)=+\infty$ for $i>j$, and for $1\le i\le j$ the recurrence minimizes between skipping job $j$ and appending an eligible final on-time batch of $1$ through $\min(B,i)$ consecutive jobs. Then the minimum tardy-job count over all complete valid batch schedules is
--
--   $$
--   U^*=n-\max\{0\le i\le n:f(i,n)<+\infty\}.
--   $$
--
--   The equality is DP3's correctness claim. Its right-hand side is computed from the paper's recurrence; $U^*$ independently minimizes over all complete schedules.
--
--   **Formalization Note** The paper's printed maximum starts at $i=1$, leaving an empty set when no job can finish on time. The corrected range starts at zero. Both release and due-date sequences are required to be nondecreasing in index; due-date order alone makes the recurrence's $r_j$ unsuitable when ties are broken against releases. The $O(n^2B)$ running-time bound is not formalized.
-- source:
--   Lee, Uzsoy & Martin-Vega, Efficient Algorithms for Scheduling Semiconductor Burn-In Operations, Oper. Res. 40(4) (1992), pp. 770–771, §4, Algorithm DP3, displayed optimal-value formula

import Mathlib
import Definitions.Def_BurnInBatch_TardyJobs_Model
import Definitions.Def_BurnInBatch_TardyJobs_DP3

namespace BurnInBatch.TardyJobs

/-- Correctness of Algorithm DP3, pp. 770–771, with zero included among
feasible on-time job counts when taking the maximum. -/
theorem dp3_correct {n : ℕ} (B p : ℕ) (r d : Fin n → ℕ)
    (hB : 0 < B) (hd : Monotone d) (hr : Monotone r) :
    n - dp3MaxOnTime B p r d = minTardy B (equalTime p) r d := by sorry

end BurnInBatch.TardyJobs
