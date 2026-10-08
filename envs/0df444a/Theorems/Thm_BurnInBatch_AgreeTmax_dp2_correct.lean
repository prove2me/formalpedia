-- Prove2me | Theorems.Thm_BurnInBatch_AgreeTmax_dp2_correct
-- name    : BurnInBatch.AgreeTmax.dp2_correct
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:29:59.481418+00:00
-- url     : https://prove2.me/theorems/995cdf2b-86ca-4967-a3c0-15ba630f291e
-- title:
--   Correctness of Algorithm DP2 — $f(j)$ is the minimum makespan of an on-time batch schedule of jobs $1,\dots,j$, and $\infty$ if none exists
-- statement:
--   Consider $n$ jobs on a single batch processing machine of capacity $B\ge 1$, all available at time $0$, with processing times $p_i$ and due dates $d_i$ in $\mathbb N$, indexed so that
--   $$d_1\le d_2\le\dots\le d_n\quad\text{and}\quad p_1\le p_2\le\dots\le p_n .$$
--   A batch takes the processing time of its longest job and batches run back to back from time $0$. Let $f$ be the value function of Algorithm DP2: $f(0)=0$ and, for $j\ge1$,
--   $$f(j)=\min_{\max\{1,j-B+1\}\le i\le j} f_i(j),\qquad f_i(j)=\begin{cases}f(i-1)+p_j,& f(i-1)+p_j\le d_i,\\ \infty,&\text{otherwise.}\end{cases}$$
--   Then for every $0\le j\le n$,
--   $$f(j)=\min\bigl\{\,C_{\max}(S)\ :\ S \text{ a batch schedule of the jobs } 1,\dots,j \text{ with } T_{\max}(S)=0\,\bigr\},$$
--   the minimum over **all** batch schedules (any batching, any order), with the convention that the minimum of the empty set is $\infty$. In particular $f(j)<\infty$ exactly when the jobs $1,\dots,j$ can be completed by their due dates, and $f(n)$ answers the feasibility question of $1/B/T_{\max}$ with agreeable processing times and due dates.
--
--   Combined with a bisection over due-date shifts, this decides the minimum $T_{\max}$; the running-time bounds $O(nB)$ and $O[nB\log_2(np_{\max})]$ are not part of this statement.
--
--   **Formalization Note** The minimum is the infimum in $\mathbb N_\infty$, where $\top=\infty$ is the infimum of the empty set. The paper's standing assumption "jobs are indexed in increasing order of due dates" is strengthened to nondecreasing due dates **and** nondecreasing processing times: DP2 charges $p_j$ for the batch $\{i,\dots,j\}$ and checks only $d_i$, which is right only under both orders. Without the second one the statement is false: for $B=2$, $p=(3,1)$, $d=(5,5)$ the recursion gives $f(2)=1$ while every schedule takes at least $3$. Agreeable data (strict form $p_i<p_j\Rightarrow d_i\le d_j$) always admit such an indexing. Jobs are 0-based in Lean; the paper's jobs $1,\dots,j$ are `jobsUpTo n j`.
-- source:
--   Lee, Uzsoy & Martin-Vega, Efficient Algorithms for Scheduling Semiconductor Burn-In Operations, Oper. Res. 40(4) (1992), p. 770, §3, Algorithm DP2 (meaning of f(j)); p. 769, last paragraph of §3 before DP2 ("to determine whether or not a feasible solution exists")

import Mathlib
import Definitions.Def_BurnInBatch_AgreeTmax_Model
import Definitions.Def_BurnInBatch_AgreeTmax_DP2

namespace BurnInBatch.AgreeTmax

/-- Correctness of Algorithm DP2 (Lee, Uzsoy & Martin-Vega 1992, §3, p. 770): with jobs indexed
so that due dates and processing times are both nondecreasing, for every prefix length `j ≤ n`,
`dp2 B p d j` is the minimum makespan over all valid batch schedules of the jobs `1, …, j` with
`T_max = 0`, and `⊤` (the infimum of the empty set in `ℕ∞`) if there is none. -/
theorem dp2_correct {n B : ℕ} (hB : 0 < B) (p d : Fin n → ℕ)
    (hd : Monotone d) (hp : Monotone p) (j : ℕ) (hj : j ≤ n) :
    dp2 B p d j =
      ⨅ (S : List (Finset (Fin n))) (_ : IsValid B (jobsUpTo n j) S ∧ Tmax p d S = 0),
        (makespan p S : ℕ∞) := by sorry

end BurnInBatch.AgreeTmax
