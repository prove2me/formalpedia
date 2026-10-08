-- Prove2me | Theorems.Thm_EmmonsTardiness_SPT_first_job_reduction
-- name    : EmmonsTardiness.SPT.first_job_reduction
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T11:30:48.078985+00:00
-- url     : https://prove2.me/theorems/f311b3af-9b36-4dab-835b-72698baec2b9
-- title:
--   p. 705 — remove the job that must be first and repeat: J_k then an optimum of the reduced problem is optimal
-- statement:
--   Let $J$ be a finite set of jobs with processing times $p_i$ and due dates $d_i$, and let $J_k \in J$. Suppose that some optimal schedule of $J$ has $J_k$ first. Consider the reduced problem on the jobs $J\setminus\{J_k\}$ with the same processing times and with due dates $d_i - p_k$. If $l'$ is an optimal schedule of the reduced problem, then the schedule
--   $$J_k,\ \text{followed by } l',$$
--   is an optimal schedule of $J$.
--
--   This is Emmons's procedure "Find the job that must be done first or last, remove it from the problem, and repeat", for a job that must be done first; the proof of Corollary 1.4 applies it repeatedly.
--
--   **Formalization Note** The SPT indexing convention passes to the reduced problem, since subtracting the common constant $p_k$ from all due dates keeps their order. No sign hypothesis on $p$ or $d$ is needed.
-- source:
--   Emmons, One-Machine Sequencing to Minimize Certain Functions of Job Tardiness, Operations Research 17(4), 1969, https://doi.org/10.1287/opre.17.4.701, p. 705, paragraph after Corollary 1.3 (general procedure and time re-referencing)

import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_EmmonsTardiness_SPT_Model

namespace EmmonsTardiness.SPT

open MooreLateJobs

/-- Emmons 1969, p. 705, paragraph after Corollary 1.3 ("Find the job that must be done first
…, remove it from the problem, and repeat"): if some optimal schedule of `J` starts with `k`,
and `l'` is an optimal schedule of the reduced problem on `J ∖ {k}` with due dates `d_i − p_k`,
then `k` followed by `l'` is an optimal schedule of `J`. (The indexing convention
`IsSPTIndexed` passes to the reduced problem, because subtracting the common constant `p_k` from
all due dates preserves their order.) -/
theorem first_job_reduction {ι : Type*} [DecidableEq ι] (p d : ι → ℝ) (J : Finset ι)
    (k : ι) (hk : k ∈ J) (hfirst : ∃ l, IsOptimal p d J l ∧ l.head? = some k)
    (l' : List ι) (hl' : IsOptimal p (fun i => d i - p k) (J.erase k) l') :
    IsOptimal p d J (k :: l') := by sorry

end EmmonsTardiness.SPT
