-- Prove2me | Theorems.Thm_EmmonsTardiness_EDD_theorem_2_star
-- name    : EmmonsTardiness.EDD.theorem_2_star
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:51:00.258923+00:00
-- url     : https://prove2.me/theorems/8d7b1a15-e1ee-4682-bf44-880901e33b14
-- title:
--   Theorem 2*, p. 713 — if k←A_k, d_j > d_k and d_j + p_j ≥ Σ_{A_k′} p_i, then k←j
-- statement:
--   Consider $n$ jobs on one machine, job $J_i$ with processing time $p_i\ge 0$ and due date $d_i$, indexed so that $j<k$ implies $p_j<p_k$, or $p_j=p_k$ and $d_j\le d_k$. Let $g$ be convex and nondecreasing on $[0,\infty)$; a schedule is optimal if it minimizes $\sum_J g(T_i)$, $T_i=\max(0,C_i-d_i)$.
--
--   **Theorem 2\*.** Let $J_j$ and $J_k$ be two jobs with $j<k$, and let $A_k\subseteq J$ be a set of jobs not containing $J_k$, with complement $A_k'=\{i: i\notin A_k\}$ in $J$. If
--
--   1. $k\leftarrow A_k$: some optimal schedule has $J_k$ before every job of $A_k$;
--   2. $d_j>d_k$; and
--   3. $$d_j+p_j\;\ge\;\sum_{i\in A_k'}p_i,$$
--
--   then $k\leftarrow j$: some optimal schedule has $J_k$ before every job of $A_k$ and before $J_j$.
--
--   This rule lets a longer job precede a shorter one, and the information it produces enlarges the sets $A_k$ used by later applications. With $A_k=\emptyset$ it gives Corollary 2.1\*.
--
--   **Formalization Note** The notation $k\leftarrow A_k$ and $k\leftarrow j$ is read existentially: hypothesis (1) is the existence of an optimal schedule (optimal against every schedule of $J$) with $J_k$ before all of $A_k$, and the conclusion keeps that property and adds $J_k$ before $J_j$. The paper's wider cumulative reading (p. 703) is not part of the statement. Hypothesis (2) is strict, as printed. Processing times are assumed nonnegative (durations); the reduction $d_i<\sum_J p_i$ of p. 703 is not assumed.
-- source:
--   Emmons, One-Machine Sequencing to Minimize Certain Functions of Job Tardiness, Operations Research 17(4), 1969, p. 713, Theorem 2* (generalizing Theorem 2, p. 705)

import Mathlib
import Definitions.Def_EmmonsTardiness_EDD_Model

namespace EmmonsTardiness.EDD

/-- Emmons 1969, p. 713, Theorem 2*: for any two jobs `J_j`, `J_k` with `j < k`, if
(1) `k ← A_k`, (2) `d_j > d_k`, and (3) `d_j + p_j ≥ Σ_{A_k′} p_i` with `A_k′ = J \ A_k`,
then `k ← j`. Hypothesis (1) and the conclusion are read existentially over optimal schedules:
if some optimal schedule has `J_k` before every job of `A_k`, then some optimal schedule has
`J_k` before every job of `A_k` and before `J_j`. -/
theorem theorem_2_star {ι : Type*} [LinearOrder ι] (g : ℝ → ℝ) (p d : ι → ℝ) (J : Finset ι)
    (hg : ConvexOn ℝ (Set.Ici 0) g) (hgm : MonotoneOn g (Set.Ici 0))
    (hp : ∀ i ∈ J, 0 ≤ p i) (hidx : EmmonsTardiness.SPT.IsSPTIndexed p d J)
    (j k : ι) (hj : j ∈ J) (hk : k ∈ J) (hjk : j < k)
    (A : Finset ι) (hAJ : A ⊆ J) (hkA : k ∉ A)
    (h1 : ∃ l : List ι, IsOptimal g p d J l ∧ ∀ i ∈ A, EmmonsTardiness.SPT.Precedes l k i)
    (h2 : d k < d j)
    (h3 : ∑ i ∈ J \ A, p i ≤ d j + p j) :
    ∃ l : List ι, IsOptimal g p d J l ∧ (∀ i ∈ A, EmmonsTardiness.SPT.Precedes l k i) ∧ EmmonsTardiness.SPT.Precedes l k j := by sorry

end EmmonsTardiness.EDD
