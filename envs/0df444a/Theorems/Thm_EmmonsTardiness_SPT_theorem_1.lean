-- Prove2me | Theorems.Thm_EmmonsTardiness_SPT_theorem_1
-- name    : EmmonsTardiness.SPT.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T11:30:20.874983+00:00
-- url     : https://prove2.me/theorems/26790bb9-9d07-4be7-8e29-6f67afe302a5
-- title:
--   Theorem 1, p. 703 — J_j may precede J_k (j<k) if d_j ≤ max(Σ_{B_k} p_i + p_k, d_k)
-- statement:
--   Let $J$ be a finite set of SPT-indexed jobs with nonnegative processing times $p_i$ and due dates $d_i$. Let $J_j, J_k\in J$ with $j<k$, and let $B\subseteq J$ with $J_k\notin B$. Assume
--
--   1. there is an optimal schedule in which every job of $B$ precedes $J_k$ (Emmons's hypothesis $B_k \leftarrow k$), and
--   2. $d_j \le \max\big(\sum_{i\in B} p_i + p_k,\ d_k\big)$.
--
--   Then there is an optimal schedule in which every job of $B$ precedes $J_k$ and, in addition, $J_j$ precedes $J_k$ (Emmons's $j\leftarrow k$):
--   $$\exists\, l \text{ optimal}:\quad B \text{ before } J_k \ \text{ and } \ J_j \text{ before } J_k \text{ in } l.$$
--
--   Theorem 1 is the paper's main tool for deciding the relative order of a shorter and a longer job; Corollaries 1.1–1.4 are its special case $B=\varnothing$.
--
--   **Formalization Note** Emmons's notation $j\leftarrow k$ means "there exists an optimal schedule that has all the properties already established and in which $J_j$ precedes $J_k$". Here the properties already established are exactly those of hypothesis (1): all of $B$ before $J_k$. The paper's wider cumulative reading, over every ordering found so far by any theorem, is argued informally on p. 702 and is not part of this statement. Processing times are assumed nonnegative (added: they are durations). The reduction $d_i < \sum_J p_i$ of p. 703 is not assumed, which makes the statement stronger.
-- source:
--   Emmons, One-Machine Sequencing to Minimize Certain Functions of Job Tardiness, Operations Research 17(4), 1969, https://doi.org/10.1287/opre.17.4.701, p. 703, Theorem 1

import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_EmmonsTardiness_SPT_Model

namespace EmmonsTardiness.SPT

open MooreLateJobs

/-- Emmons 1969, Theorem 1, p. 703: for jobs `j < k` (SPT indexing), if (1) some optimal schedule
has every job of `B` (the jobs already known to precede `J_k`, `k ∉ B`) before `k`, and
(2) `d_j ≤ max(Σ_{i∈B} p_i + p_k, d_k)`, then some optimal schedule has every job of `B` before
`k` and also `j` before `k` ("j ← k"). "The properties already established" of the paper's
cumulative notation are taken to be exactly those of hypothesis (1). Processing times are
assumed nonnegative (added, disclosed). -/
theorem theorem_1 {ι : Type*} [LinearOrder ι] (p d : ι → ℝ) (J : Finset ι)
    (hp : ∀ i ∈ J, 0 ≤ p i) (hidx : IsSPTIndexed p d J)
    (j k : ι) (hj : j ∈ J) (hk : k ∈ J) (hjk : j < k)
    (B : Finset ι) (hB : B ⊆ J) (hkB : k ∉ B)
    (h1 : ∃ l, IsOptimal p d J l ∧ ∀ i ∈ B, Precedes l i k)
    (h2 : d j ≤ max ((∑ i ∈ B, p i) + p k) (d k)) :
    ∃ l, IsOptimal p d J l ∧ (∀ i ∈ B, Precedes l i k) ∧ Precedes l j k := by sorry

end EmmonsTardiness.SPT
