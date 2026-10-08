-- Prove2me | Theorems.Thm_EmmonsTardiness_SPT_corollary_1_4
-- name    : EmmonsTardiness.SPT.corollary_1_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T11:31:04.305989+00:00
-- url     : https://prove2.me/theorems/e9e05a47-ffb4-4bb8-97cc-854a7fdc3ef2
-- title:
--   Corollary 1.4, p. 705 — the SPT schedule minimizes total tardiness if d_j + p_j ≤ p_1 + ⋯ + p_{j+1}
-- statement:
--   Let $J=\{J_1,\dots,J_n\}$ be a finite set of jobs on one machine, with nonnegative processing times $p_i$ and due dates $d_i$, indexed in order of nondecreasing processing times and, in case of equality, of nondecreasing due dates. The SPT schedule processes $J_1, J_2, \dots, J_n$ in this order. If
--   $$d_j + p_j \le \sum_{i=1}^{j+1} p_i \qquad\text{for } j = 1, \dots, n-1,$$
--   then the SPT schedule minimizes the total tardiness $\sum_{i\in J}\max(0, C_i - d_i)$ over all schedules of $J$.
--
--   With $C_j=\sum_{i\le j}p_i$ the SPT completion time of $J_j$, the condition reads $d_j \le C_j + (p_{j+1} - p_j)$. It contains the classical fact that the SPT schedule is optimal when every job is tardy under it, and it allows a job to be early as long as its due date does not exceed its SPT completion time by more than $p_{j+1}-p_j$.
--
--   **Formalization Note** The SPT schedule $L$ lists the jobs in index order; the paper's 1-based job $J_j$ is the 0-based entry $L[m]$ with $m=j-1$, the sum $\sum_{i=1}^{j+1}p_i$ is the completion time of position $m+1$ of $L$, and the range $j=1,\dots,n-1$ is $m+1<n$. Optimality is against every schedule of $J$. Processing times are assumed nonnegative (added: they are durations). The reduction $d_i < \sum_J p_i$ of p. 703 is not assumed, which makes the statement stronger. For $J=\varnothing$ or a single job the statement holds trivially.
-- source:
--   Emmons, One-Machine Sequencing to Minimize Certain Functions of Job Tardiness, Operations Research 17(4), 1969, https://doi.org/10.1287/opre.17.4.701, p. 705, Corollary 1.4

import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_EmmonsTardiness_SPT_Model

namespace EmmonsTardiness.SPT

open MooreLateJobs

/-- Emmons 1969, Corollary 1.4, p. 705: the SPT schedule is optimal if
`d_j + p_j ≤ Σ_{i=1}^{j+1} p_i` for `j = 1, …, n − 1`.

Index translation: `L = sptSchedule J` lists the jobs `J_1, …, J_n` in index order, so the
paper's 1-based job `J_j` is the 0-based entry `L[m]` with `m = j − 1`; the right-hand side
`Σ_{i=1}^{j+1} p_i` is the SPT completion time of `J_{j+1}`, i.e. `completionAt p L (m + 1)` (the
sum of the first `m + 2 = j + 1` processing times); and the range `j = 1, …, n − 1` is
`m + 1 < L.length`. Processing times are assumed nonnegative (added, disclosed). The reduction
`d_i < Σ_J p` of p. 703 is not imposed. -/
theorem corollary_1_4 {ι : Type*} [LinearOrder ι] (p d : ι → ℝ) (J : Finset ι)
    (hp : ∀ i ∈ J, 0 ≤ p i) (hidx : IsSPTIndexed p d J)
    (hcond : ∀ (m : ℕ) (hm : m + 1 < (sptSchedule J).length),
      d ((sptSchedule J)[m]'(by omega)) + p ((sptSchedule J)[m]'(by omega)) ≤
        Shared.completionAt p (sptSchedule J) (m + 1)) :
    IsOptimal p d J (sptSchedule J) := by sorry

end EmmonsTardiness.SPT
