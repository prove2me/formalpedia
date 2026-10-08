-- Prove2me | Theorems.Thm_BurnInBatch_ReleaseTmax_consecutive_batches
-- name    : BurnInBatch.ReleaseTmax.consecutive_batches
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:28:49.622185+00:00
-- url     : https://prove2.me/theorems/2cd89510-08c0-4642-a2d7-79ffd80244e2
-- title:
--   §3, justification of DP1 — some minimum-makespan on-time schedule has consecutive batches
-- statement:
--   Consider one batch machine of capacity $B \ge 1$ and $n$ jobs with common processing time $p$, release times $r_i$ and due dates $d_i$, indexed so that
--   $$
--   d_1 \le d_2 \le \dots \le d_n \quad\text{and}\quad r_1 \le r_2 \le \dots \le r_n .
--   $$
--   Fix $0 \le j \le n$ and let $S$ be a batch schedule of jobs $1, \dots, j$ in which every job is on time. Then there is a batch schedule $S'$ of jobs $1, \dots, j$ in which every job is on time, every batch consists of consecutively indexed jobs $\{i, i+1, \dots, k\}$ (at most $B$ of them), the batches appear in increasing index order, and
--   $$
--   C_{\max}(S') \le C_{\max}(S).
--   $$
--   In particular, if an on-time schedule of jobs $1, \dots, j$ exists, some on-time schedule of minimum makespan is a consecutive partition of $1, \dots, j$ into blocks of at most $B$ jobs. This is the claim that turns the problem into the consecutive partition problem solved by Algorithm DP1.
--
--   **Formalization Note** The paper assumes that the jobs are indexed in increasing order of due dates. Here the index order is nondecreasing in both $d$ and $r$: with ties in $d$ ordered against $r$ the claim fails (two jobs, $B = 2$, $p = 1$, $d = (2,2)$, $r = (1,0)$: the consecutive DP value is $1$ but no schedule finishes before $2$). Such an indexing exists whenever release times and due dates are agreeable (sort by $(d, r)$), and the two monotonicity conditions imply strict-form agreeability. The makespan clause is the content of the proof of Lemma 1 ("the completion times of the batches after the exchange … will not be greater"), which the justification of DP1 relies on.
-- source:
--   Lee, Uzsoy & Martin-Vega, Efficient Algorithms for Scheduling Semiconductor Burn-In Operations, Oper. Res. 40(4) (1992), p. 768, §3, justification of DP1 ("To justify DP1, note that each batch will contain no more than B consecutively indexed jobs …")

import Mathlib
import Definitions.Def_BurnInBatch_ReleaseTmax_Model

namespace BurnInBatch.ReleaseTmax

/-- Justification of DP1 (§3, p. 768): with the jobs indexed in nondecreasing order of due dates
and of release times, every on-time batch schedule `S` of the first `j` jobs can be replaced by
an on-time batch schedule `S'` of the same jobs whose batches are blocks of consecutively indexed
jobs (at most `B` each, as in every batch schedule), in increasing index order, with makespan no
larger than that of `S`. -/
theorem consecutive_batches {n : ℕ} (B p : ℕ) (r d : Fin n → ℕ) (hB : 0 < B)
    (hd : Monotone d) (hr : Monotone r) (j : ℕ) (hj : j ≤ n)
    (S : List (Finset (Fin n))) (hS : IsBatchSchedule B (prefixJobs n j) S)
    (hon : AllOnTime p r d (prefixJobs n j) S) :
    ∃ S' : List (Finset (Fin n)),
      IsBatchSchedule B (prefixJobs n j) S' ∧ AllOnTime p r d (prefixJobs n j) S' ∧
      IsConsecutive S' ∧ makespan p r S' ≤ makespan p r S := by sorry

end BurnInBatch.ReleaseTmax
