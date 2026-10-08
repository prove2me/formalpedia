-- Prove2me | Theorems.Thm_EmmonsTardiness_SPT_corollary_1_1
-- name    : EmmonsTardiness.SPT.corollary_1_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T11:30:35.403001+00:00
-- url     : https://prove2.me/theorems/6361d8c0-ac3e-45db-b91e-b7a1c84e9f55
-- title:
--   Corollary 1.1, p. 704 — J_1 is first in an optimal schedule if d_1 ≤ max(p_i, d_i) for all i > 1
-- statement:
--   Let $J$ be a nonempty finite set of SPT-indexed jobs with nonnegative processing times $p_i$ and due dates $d_i$, and let $J_1$ be the job of least index. If
--   $$d_1 \le \max(p_i, d_i)\qquad\text{for every job } J_i \text{ with } i>1,$$
--   then there is an optimal schedule whose first job is $J_1$.
--
--   This corollary is the case $B_k=\varnothing$ of Theorem 1 applied to $J_1$ and every later job. It is the step that fixes the first job in the proof of Corollary 1.4.
--
--   **Formalization Note** $J_1$ is the minimum of $J$ in the index order. Processing times are assumed nonnegative (added: they are durations). The reduction $d_i < \sum_J p_i$ of p. 703 is not assumed.
-- source:
--   Emmons, One-Machine Sequencing to Minimize Certain Functions of Job Tardiness, Operations Research 17(4), 1969, https://doi.org/10.1287/opre.17.4.701, p. 704, Corollary 1.1

import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_EmmonsTardiness_SPT_Model

namespace EmmonsTardiness.SPT

open MooreLateJobs

/-- Emmons 1969, Corollary 1.1, p. 704: if the first job `J_1` in the SPT indexing (the least
element of `J`) satisfies `d_1 ≤ max(p_i, d_i)` for every other job `i > 1`, then `J_1` is first
in an optimal schedule. Processing times are assumed nonnegative (added, disclosed). -/
theorem corollary_1_1 {ι : Type*} [LinearOrder ι] (p d : ι → ℝ) (J : Finset ι)
    (hp : ∀ i ∈ J, 0 ≤ p i) (hidx : IsSPTIndexed p d J) (hJ : J.Nonempty)
    (h : ∀ i ∈ J, J.min' hJ < i → d (J.min' hJ) ≤ max (p i) (d i)) :
    ∃ l, IsOptimal p d J l ∧ l.head? = some (J.min' hJ) := by sorry

end EmmonsTardiness.SPT
