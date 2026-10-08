-- Prove2me | Theorems.Thm_EmmonsTardiness_EDD_corollary_2_2_star
-- name    : EmmonsTardiness.EDD.corollary_2_2_star
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:51:20.849079+00:00
-- url     : https://prove2.me/theorems/45addfe9-0cc4-4d31-9273-4a5b13b4f7b2
-- title:
--   Corollary 2.2*, p. 713 — the EDD schedule minimizes Σ g(T_i) for convex nondecreasing g if W_i ≤ d_i for all i
-- statement:
--   Consider a finite set $J$ of jobs on one machine, all available at time $0$; job $J_i$ has processing time $p_i\ge 0$ and due date $d_i$. In a schedule, $C_i$ is the completion time of $J_i$, $W_i=C_i-p_i$ its waiting (starting) time and $T_i=\max(0,C_i-d_i)$ its tardiness. Let $g$ be convex and nondecreasing on $[0,\infty)$.
--
--   **Corollary 2.2\*.** Let $l$ be an EDD schedule of $J$, i.e. the jobs are sequenced in order of nondecreasing due dates. If it produces
--   $$W_i\le d_i\qquad\text{for all } i\in J,$$
--   then $l$ minimizes $\sum_{i\in J} g(T_i)$ over all schedules of $J$.
--
--   The condition $W_i\le d_i$ is equivalent to $C_i\le d_i+p_i$: each job may be tardy, but by no more than its own processing time. The classical result says that the EDD schedule is optimal if at most one job is tardy; here any or all jobs may be tardy, and the conclusion holds for every penalty that is a convex nondecreasing function of tardiness, total tardiness ($g(T)=T$, Corollary 2.2) being one case.
--
--   **Formalization Note** "The EDD schedule" is any schedule of $J$ whose due dates are nondecreasing along the sequence; ties are broken arbitrarily, and the statement holds for every tie-break. Optimality is against every schedule of $J$. Convexity and monotonicity of $g$ are assumed on $[0,\infty)$ only, where the tardiness values lie. Processing times are assumed nonnegative (durations); the reduction $d_i<\sum_J p_i$ of p. 703 is not assumed. The page's "increasing" is read as nondecreasing, as in the paper's abstract and introduction.
-- source:
--   Emmons, One-Machine Sequencing to Minimize Certain Functions of Job Tardiness, Operations Research 17(4), 1969, p. 713, Corollary 2.2* (generalizing Corollary 2.2, p. 706)

import Mathlib
import Definitions.Def_EmmonsTardiness_EDD_Model

namespace EmmonsTardiness.EDD

/-- Emmons 1969, p. 713, Corollary 2.2*: for a loss function `g` convex and nondecreasing on
`[0, ∞)`, the EDD schedule is optimal for `Σ_J g(T_i)` if it produces starting times
`W_i ≤ d_i` for all `i`. -/
theorem corollary_2_2_star {ι : Type*} [DecidableEq ι] (g : ℝ → ℝ) (p d : ι → ℝ)
    (J : Finset ι)
    (hg : ConvexOn ℝ (Set.Ici 0) g) (hgm : MonotoneOn g (Set.Ici 0))
    (hp : ∀ i ∈ J, 0 ≤ p i)
    (l : List ι) (hl : MooreLateJobs.Shared.IsSchedule J l) (hedd : IsEDDOrder d l)
    (hW : ∀ i ∈ J, startTime p l i ≤ d i) :
    IsOptimal g p d J l := by sorry

end EmmonsTardiness.EDD
