-- Prove2me | Theorems.Thm_EmmonsTardiness_EDD_corollary_2_1_star
-- name    : EmmonsTardiness.EDD.corollary_2_1_star
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:50:57.101978+00:00
-- url     : https://prove2.me/theorems/e65bacc9-505f-4fce-8d10-04c038d58855
-- title:
--   Corollary 2.1*, p. 713 — if d_j = max_i d_i and d_j + p_j ≥ p, then J_j is last in an optimal schedule
-- statement:
--   Consider a finite set $J$ of jobs on one machine, job $J_i$ with processing time $p_i\ge 0$ and due date $d_i$, and write $p=\sum_{i\in J}p_i$ for the total processing time. Let $g$ be convex and nondecreasing on $[0,\infty)$; a schedule is optimal if it minimizes $\sum_J g(T_i)$, $T_i=\max(0,C_i-d_i)$.
--
--   **Corollary 2.1\*.** If $J_j\in J$ has the latest due date, $d_j=\max_i\{d_i\}$, and
--   $$d_j+p_j\ \ge\ p,$$
--   then $J_j$ is last: there is an optimal schedule whose last job is $J_j$.
--
--   The corollary removes one job from the end of the sequence; repeated together with the last-job reduction it proves Corollary 2.2\*.
--
--   **Formalization Note** "$J_j$ is last" is stated as the existence of an optimal schedule (optimal against every schedule of $J$) ending in $J_j$. Ties for the maximum due date are allowed, as on the page ($d_j$ is a maximum, not the unique one). The statement does not use the job indices. Processing times are assumed nonnegative (durations); the reduction $d_i<p$ of p. 703 is not assumed.
-- source:
--   Emmons, One-Machine Sequencing to Minimize Certain Functions of Job Tardiness, Operations Research 17(4), 1969, p. 713, Corollary 2.1* (generalizing Corollary 2.1, p. 706)

import Mathlib
import Definitions.Def_EmmonsTardiness_EDD_Model

namespace EmmonsTardiness.EDD

/-- Emmons 1969, p. 713, Corollary 2.1*: if `d_j = max_i {d_i}` and `d_j + p_j ≥ p = Σ_J p_i`,
then `J_j` is last in some schedule minimizing `Σ_J g(T_i)`. -/
theorem corollary_2_1_star {ι : Type*} [DecidableEq ι] (g : ℝ → ℝ) (p d : ι → ℝ)
    (J : Finset ι)
    (hg : ConvexOn ℝ (Set.Ici 0) g) (hgm : MonotoneOn g (Set.Ici 0))
    (hp : ∀ i ∈ J, 0 ≤ p i)
    (j : ι) (hj : j ∈ J) (hmax : ∀ i ∈ J, d i ≤ d j)
    (hlast : ∑ i ∈ J, p i ≤ d j + p j) :
    ∃ l : List ι, IsOptimal g p d J l ∧ l.getLast? = some j := by sorry

end EmmonsTardiness.EDD
