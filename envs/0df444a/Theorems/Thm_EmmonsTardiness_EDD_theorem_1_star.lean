-- Prove2me | Theorems.Thm_EmmonsTardiness_EDD_theorem_1_star
-- name    : EmmonsTardiness.EDD.theorem_1_star
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:50:55.726632+00:00
-- url     : https://prove2.me/theorems/4316cde5-3210-4518-945a-5b156e689d27
-- title:
--   Theorem 1*, p. 713 — for j < k, if d_j ≤ d_k then J_j precedes J_k in a schedule minimizing Σ g(T_i)
-- statement:
--   Consider $n$ jobs on one machine, job $J_i$ with processing time $p_i\ge 0$ and due date $d_i$, indexed so that $j<k$ implies $p_j<p_k$, or $p_j=p_k$ and $d_j\le d_k$. Let $g$ be convex and nondecreasing on $[0,\infty)$, and call a schedule optimal if it minimizes $\sum_J g(T_i)$, where $T_i=\max(0,C_i-d_i)$ is the tardiness of $J_i$.
--
--   **Theorem 1\*.** For any two jobs $J_j$ and $J_k$ with $j<k$, if
--   $$d_j\le d_k,$$
--   then $j\leftarrow k$: there is an optimal schedule in which $J_j$ precedes $J_k$.
--
--   For total tardiness, Theorem 1 of the paper allows $J_j$ before $J_k$ under the weaker condition $d_j\le\max(\sum_{B_k}p_i+p_k,\,d_k)$; for a general convex penalty only the part $d_j\le d_k$ survives. Theorem 1\* is the basic ordering rule for the generalized objective and gives Corollary 1.3\*.
--
--   **Formalization Note** "$j\leftarrow k$" is stated as the existence of an optimal schedule (optimal against every schedule of $J$) in which $J_j$ comes before $J_k$; the paper's cumulative reading ("has all the properties already established", p. 703) is not part of the statement. Processing times are assumed nonnegative (they are durations). The reduction $d_i<\sum_J p_i$ of p. 703 is not assumed, so the statement covers more instances than the page's.
-- source:
--   Emmons, One-Machine Sequencing to Minimize Certain Functions of Job Tardiness, Operations Research 17(4), 1969, p. 713, Theorem 1*

import Mathlib
import Definitions.Def_EmmonsTardiness_EDD_Model

namespace EmmonsTardiness.EDD

/-- Emmons 1969, p. 713, Theorem 1*: for any two jobs `J_j`, `J_k` with `j < k`, if `d_j ≤ d_k`
then `j ← k`: some schedule minimizing `Σ_J g(T_i)` has `J_j` before `J_k`. -/
theorem theorem_1_star {ι : Type*} [LinearOrder ι] (g : ℝ → ℝ) (p d : ι → ℝ) (J : Finset ι)
    (hg : ConvexOn ℝ (Set.Ici 0) g) (hgm : MonotoneOn g (Set.Ici 0))
    (hp : ∀ i ∈ J, 0 ≤ p i) (hidx : EmmonsTardiness.SPT.IsSPTIndexed p d J)
    (j k : ι) (hj : j ∈ J) (hk : k ∈ J) (hjk : j < k) (hd : d j ≤ d k) :
    ∃ l : List ι, IsOptimal g p d J l ∧ EmmonsTardiness.SPT.Precedes l j k := by sorry

end EmmonsTardiness.EDD
