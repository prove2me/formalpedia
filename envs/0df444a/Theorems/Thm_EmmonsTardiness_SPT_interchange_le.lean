-- Prove2me | Theorems.Thm_EmmonsTardiness_SPT_interchange_le
-- name    : EmmonsTardiness.SPT.interchange_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T11:29:51.552636+00:00
-- url     : https://prove2.me/theorems/8011c697-66f9-491f-9955-af38192cfe39
-- title:
--   Proof of Theorem 1, p. 703 — interchanging J_j and J_k does not increase total tardiness
-- statement:
--   Let $J$ be a finite set of SPT-indexed jobs with nonnegative processing times $p_i$ and due dates $d_i$. Let $J_j, J_k \in J$ with $j<k$, and let $B\subseteq J$ be a set of jobs. Suppose that
--   $$d_j \le \max\Big(\sum_{i\in B} p_i + p_k,\ d_k\Big).$$
--   Let $l$ be a schedule of $J$ in which every job of $B$ precedes $J_k$, and $J_k$ precedes $J_j$. Let $l^{\ast}$ be the schedule obtained from $l$ by interchanging $J_j$ and $J_k$. Then
--
--   1. $l^{\ast}$ is a schedule of $J$;
--   2. every job of $B$ precedes $J_k$ in $l^{\ast}$;
--   3. $J_j$ precedes $J_k$ in $l^{\ast}$;
--   4. the total tardiness does not increase: $T(l^{\ast}) \le T(l)$.
--
--   This is the claim on which Emmons's proof of Theorem 1 rests: in a schedule that satisfies hypothesis (1) and places $J_k$ before $J_j$, the interchange "must decrease, or possibly leave unchanged, the total tardiness".
--
--   **Formalization Note** The interchange is the list obtained by applying the transposition of $j$ and $k$ to every entry of $l$. Processing times are assumed nonnegative (they are durations; the page uses that the start time of $J_k$ is at least $\sum_{B} p_i$). Conclusions 1–3 are the bookkeeping that the interchanged schedule keeps the properties already established. The reduction $d_i < \sum_J p_i$ of p. 703 is not assumed.
-- source:
--   Emmons, One-Machine Sequencing to Minimize Certain Functions of Job Tardiness, Operations Research 17(4), 1969, https://doi.org/10.1287/opre.17.4.701, p. 703, proof of Theorem 1, first paragraph (argued through cases (a), (b) and Fig. 1, pp. 703–704)

import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_EmmonsTardiness_SPT_Model

namespace EmmonsTardiness.SPT

open MooreLateJobs

/-- Emmons 1969, proof of Theorem 1, p. 703, first paragraph: in a schedule satisfying
hypothesis (1) (every job of `B` precedes `k`) in which `k` precedes `j`, interchanging `j` and
`k` does not increase total tardiness, provided `j < k` in the SPT indexing and hypothesis (2)
`d_j ≤ max(Σ_{i∈B} p_i + p_k, d_k)` holds. The interchanged sequence `l.map (Equiv.swap j k)` is
again a schedule of `J`, with `j` before `k` and every job of `B` still before `k`; these
companion facts are stated as the first three conjuncts. Processing times are assumed
nonnegative (an added, disclosed hypothesis: they are durations). -/
theorem interchange_le {ι : Type*} [LinearOrder ι] (p d : ι → ℝ) (J : Finset ι)
    (hp : ∀ i ∈ J, 0 ≤ p i) (hidx : IsSPTIndexed p d J)
    (j k : ι) (hj : j ∈ J) (hk : k ∈ J) (hjk : j < k)
    (B : Finset ι) (hB : B ⊆ J)
    (h2 : d j ≤ max ((∑ i ∈ B, p i) + p k) (d k))
    (l : List ι) (hl : Shared.IsSchedule J l)
    (hBl : ∀ i ∈ B, Precedes l i k) (hkj : Precedes l k j) :
    Shared.IsSchedule J (l.map (Equiv.swap j k)) ∧
      (∀ i ∈ B, Precedes (l.map (Equiv.swap j k)) i k) ∧
      Precedes (l.map (Equiv.swap j k)) j k ∧
      totalTardiness p d J (l.map (Equiv.swap j k)) ≤ totalTardiness p d J l := by sorry

end EmmonsTardiness.SPT
