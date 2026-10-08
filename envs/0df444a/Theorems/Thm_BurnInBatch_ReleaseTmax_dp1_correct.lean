-- Prove2me | Theorems.Thm_BurnInBatch_ReleaseTmax_dp1_correct
-- name    : BurnInBatch.ReleaseTmax.dp1_correct
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T14:09:00.667367+00:00
-- url     : https://prove2.me/theorems/cefa3def-1614-4117-810a-6ef0915f521e
-- title:
--   §3 — Algorithm DP1 computes the minimum makespan of an on-time batch schedule, and $\infty$ when none exists
-- statement:
--   Consider one batch machine of capacity $B \ge 1$ and $n$ jobs with common processing time $p$, release times $r_i$ and due dates $d_i$, indexed so that
--   $$
--   d_1 \le \dots \le d_n \quad\text{and}\quad r_1 \le \dots \le r_n .
--   $$
--   Let $f$ be the value of Algorithm DP1. Then for every $0 \le j \le n$,
--   $$
--   f(j) = \min\bigl\{\, C_{\max}(S) \;:\; S \text{ a batch schedule of jobs } 1, \dots, j \text{ with } C_i \le d_i \text{ for all } i \le j \,\bigr\},
--   $$
--   with the minimum of the empty set equal to $\infty$. That is, $f(j)$ is finite exactly when jobs $1, \dots, j$ can be scheduled with no tardy job, and then it is the minimum makespan of such a schedule; the minimum ranges over all batch schedules (any batching, any order). For $j = n$ this is the paper's claim that DP1 "will find a feasible schedule with minimum makespan if a feasible schedule exists".
--
--   The result solves the feasibility version of $1/r_i, p_i = p, B/T_{\max}$, and with due dates shifted by a trial value of $T_{\max}$ it is the subroutine of the bisection procedure for minimizing $T_{\max}$.
--
--   **Formalization Note** The paper's "jobs are indexed in increasing order of due dates" is formalized as an index order nondecreasing in both $d$ and $r$; DP1 uses $r_j$ as the release time of the batch $\{i, \dots, j\}$, and with ties in $d$ ordered against $r$ the claim is false (two jobs, $B = 2$, $p = 1$, $d = (2,2)$, $r = (1,0)$: $f(2) = 1$, optimum $2$). This index order exists whenever release times and due dates are agreeable, and implies agreeability. The minimum is an infimum in $\mathbb N_\infty$, where the infimum of the empty set is $\top = \infty$. The paper's remark "if $f(j) \le d_j$ … none are tardy" is not part of the statement. The $O(nB)$ running time is not formalized.
-- source:
--   Lee, Uzsoy & Martin-Vega, Efficient Algorithms for Scheduling Semiconductor Burn-In Operations, Oper. Res. 40(4) (1992), p. 768, §3 ("We can now state the dynamic programming algorithm DP1 which will find a feasible schedule with minimum makespan if a feasible schedule exists"), Algorithm DP1; p. 767, §3 ("will find the feasible sequence with minimum completion time if one exists")

import Mathlib
import Definitions.Def_BurnInBatch_ReleaseTmax_Model
import Definitions.Def_BurnInBatch_ReleaseTmax_DP1

namespace BurnInBatch.ReleaseTmax

/-- Correctness of Algorithm DP1 (§3, p. 768). One batch machine of capacity `B ≥ 1`, `n` jobs
with common processing time `p`, release times `r` and due dates `d`, indexed so that both `d`
and `r` are nondecreasing. For every prefix length `j ≤ n`, the DP1 value `f(j)` equals the
minimum makespan over all batch schedules of jobs `1, …, j` in which every job is on time, and
it is `⊤ = ∞` exactly when there is no such schedule (an infimum over the empty set in `ℕ∞`). -/
theorem dp1_correct {n : ℕ} (B p : ℕ) (r d : Fin n → ℕ) (hB : 0 < B)
    (hd : Monotone d) (hr : Monotone r) (j : ℕ) (hj : j ≤ n) :
    dp1 B p r d j =
      ⨅ (S : List (Finset (Fin n)))
        (_ : IsBatchSchedule B (prefixJobs n j) S ∧ AllOnTime p r d (prefixJobs n j) S),
        (makespan p r S : ℕ∞) := by sorry

end BurnInBatch.ReleaseTmax
