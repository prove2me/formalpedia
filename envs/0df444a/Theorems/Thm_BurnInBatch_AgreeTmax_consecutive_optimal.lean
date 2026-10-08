-- Prove2me | Theorems.Thm_BurnInBatch_AgreeTmax_consecutive_optimal
-- name    : BurnInBatch.AgreeTmax.consecutive_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:29:44.215521+00:00
-- url     : https://prove2.me/theorems/8d9c0654-bbb6-4090-b927-c2f23daff984
-- title:
--   Justification of DP2 — some minimum-makespan schedule with $T_{\max}=0$ is a consecutive partition
-- statement:
--   Consider $n$ jobs on a single batch processing machine of capacity $B\ge 1$, all available at time $0$, with processing times $p_i$ and due dates $d_i$, indexed so that
--   $$d_1\le d_2\le\dots\le d_n\quad\text{and}\quad p_1\le p_2\le\dots\le p_n .$$
--   Fix $j\le n$. If the jobs $1,\dots,j$ have a batch schedule with $T_{\max}=0$, then among all such schedules there is one of minimum makespan that is a **consecutive partition**: each batch is a set $\{i,i+1,\dots,k\}$ of consecutively indexed jobs (of at most $B$ jobs), and the batches are processed in increasing order of index.
--
--   This is the step by which the paper reduces $1/B/T_{\max}$ with agreeable processing times and due dates to a consecutive partition problem, which Algorithm DP2 solves.
--
--   **Formalization Note** The paper's "jobs are indexed in increasing order of due dates" (p. 767) is taken together with nondecreasing processing times. Agreeable data (strict form, $p_i<p_j\Rightarrow d_i\le d_j$) always admit such an indexing (sort by due date, then by processing time), and the pair implies agreeability. With ties in $d$ broken against $p$ the DP of the next statement is wrong, which is why both orders are assumed. Minimality is over all valid schedules of the first $j$ jobs with $T_{\max}=0$.
-- source:
--   Lee, Uzsoy & Martin-Vega, Efficient Algorithms for Scheduling Semiconductor Burn-In Operations, Oper. Res. 40(4) (1992), p. 770, §3, justification of Algorithm DP2, by reference to the justification of Algorithm DP1, p. 768

import Mathlib
import Definitions.Def_BurnInBatch_AgreeTmax_Model

namespace BurnInBatch.AgreeTmax

/-- Justification of Algorithm DP2 (p. 770, by reference to that of DP1, p. 768): with jobs
indexed so that due dates and processing times are both nondecreasing, if the jobs `1, …, j`
(`j ≤ n`) can be scheduled with `T_max = 0`, then among such schedules one of minimum makespan
is a consecutive partition: its batches are sets of consecutively indexed jobs, in increasing
order of index. -/
theorem consecutive_optimal {n B : ℕ} (hB : 0 < B) (p d : Fin n → ℕ)
    (hd : Monotone d) (hp : Monotone p) (j : ℕ) (hj : j ≤ n)
    (hfeas : ∃ S : List (Finset (Fin n)), IsValid B (jobsUpTo n j) S ∧ Tmax p d S = 0) :
    ∃ S : List (Finset (Fin n)), IsValid B (jobsUpTo n j) S ∧ Tmax p d S = 0 ∧
      IsConsecutive S ∧
      ∀ S' : List (Finset (Fin n)), IsValid B (jobsUpTo n j) S' → Tmax p d S' = 0 →
        makespan p S ≤ makespan p S' := by sorry

end BurnInBatch.AgreeTmax
