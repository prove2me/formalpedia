-- Prove2me | Theorems.Thm_EmmonsTardiness_EDD_last_job_reduction
-- name    : EmmonsTardiness.EDD.last_job_reduction
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:51:21.276474+00:00
-- url     : https://prove2.me/theorems/4864d581-d249-4fa0-bc83-a9f3f3eeefd7
-- title:
--   Proof of Corollary 2.2, p. 706 — a job known to be last can be removed and the rest scheduled optimally
-- statement:
--   Consider a finite set $J$ of jobs on one machine with processing times $p_i$ and due dates $d_i$, and any loss function $g$; a schedule is optimal if it minimizes $\sum_J g(T_i)$, $T_i=\max(0,C_i-d_i)$.
--
--   Suppose $J_j\in J$ is last in some optimal schedule of $J$. If $l'$ is an optimal schedule of the remaining jobs $J\setminus\{J_j\}$ (with the same processing times and due dates), then the schedule
--   $$l'\ \text{followed by}\ J_j$$
--   is an optimal schedule of $J$.
--
--   This is the step "Remove it from the problem, redefine $p$, and repeat" of the proof of Corollary 2.2: once a job is known to be last, the problem reduces to the remaining jobs, whose completion times are unchanged by appending $J_j$ at the end.
--
--   **Formalization Note** No property of $g$ or of the processing times is needed. "Redefine $p$" is automatic: the total processing time of the reduced problem is the sum over $J\setminus\{J_j\}$.
-- source:
--   Emmons, One-Machine Sequencing to Minimize Certain Functions of Job Tardiness, Operations Research 17(4), 1969, p. 706, proof of Corollary 2.2, last sentence

import Mathlib
import Definitions.Def_EmmonsTardiness_EDD_Model

namespace EmmonsTardiness.EDD

/-- Emmons 1969, p. 706, proof of Corollary 2.2, last sentence ("Remove it from the problem,
redefine p, and repeat"): if some optimal schedule of `J` ends with `J_j`, then appending `J_j`
to any optimal schedule of the remaining jobs `J \ {J_j}` gives an optimal schedule of `J`. -/
theorem last_job_reduction {ι : Type*} [DecidableEq ι] (g : ℝ → ℝ) (p d : ι → ℝ)
    (J : Finset ι) (j : ι) (hj : j ∈ J)
    (hlast : ∃ l : List ι, IsOptimal g p d J l ∧ l.getLast? = some j)
    (l' : List ι) (hl' : IsOptimal g p d (J.erase j) l') :
    IsOptimal g p d J (l' ++ [j]) := by sorry

end EmmonsTardiness.EDD
