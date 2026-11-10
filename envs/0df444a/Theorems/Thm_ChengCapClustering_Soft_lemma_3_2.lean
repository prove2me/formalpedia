-- Prove2me | Theorems.Thm_ChengCapClustering_Soft_lemma_3_2
-- name    : ChengCapClustering.Soft.lemma_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:52:10.401117+00:00
-- url     : https://prove2.me/theorems/0735052a-8734-45c4-bb62-28c2fc231b3b
-- title:
--   Lemma 3.2 — 2k centers suffice: the blocks of an uncapacitated solution form a block partition with $m<2k$ and $A$ equal to its cost
-- statement:
--   Let $U$ be the uniform capacity, $n\le kU$ (with $0<k<n$, $U>0$, $z\ge1$). Let $S$ be an uncapacitated solution with at most $k$ centers at locations in $F$, and split every cluster $Q$ of $S$ into $\lceil |Q|/U\rceil$ nonempty blocks of at most $U$ clients each, the representative of each block being the center of its cluster (§3.1). Then these blocks form a block partition (Definition 3.1) with $m<2k$ blocks, and its total internal cost $A$ equals the cost of $S$.
--
--   Differences from the source:
--   - generalization: an uncapacitated solution (clients assigned to a closest center) → a family of at most k centers with an arbitrary assignment in any metric space and any location set F, cost = sum over clients of the assigned distance^z; reason: the splitting and counting use neither a closest-center assignment nor the finite-F and joint-doubling assumptions of Section 3; every source instance is included
--   - encoding: "the blocks of any uncapacitated solution" (each cluster split arbitrarily into ⌈|Q|/U⌉ blocks of at most U clients, §3.1) → a block partition B with a map κ from blocks to centers such that assign = κ ∘ block, rep = loc ∘ κ, every block nonempty of size ≤ U, and exactly ⌈load_j / U⌉ blocks per center j; reason: the splitting of §3.1 written as properties of B
--   - encoding: m ≤ 2k − 1 → numBlocks + 1 ≤ 2k; reason: integer form, no natural-number subtraction
-- source:
--   Cheng, Mo, Ding 2026, Constant-Factor Approximation for Capacitated Clustering in Low Dimension with (1+ε)k Centers, arXiv:2610.40625 (held manuscript SHA-256 9d298191e7086ee0bbea53e5a3e4e9b0fe88c438ed58257f01f3c524a8ac4edb; arXiv version suffix unresolved, citation hold), Lemma 3.2, printed p. 7 / PDF p. 9

import Mathlib
import Definitions.Def_ChengCapClustering_Soft_Clustering

universe u

namespace ChengCapClustering.Soft

/-- Lemma 3.2 (2k centers suffice), printed p. 7 / PDF p. 9. With uniform capacity `U` and
`n ≤ kU`, splitting every cluster `Q` of an uncapacitated solution with at most `k` centers into
`⌈|Q|/U⌉` nonempty blocks of at most `U` clients, each represented by the cluster's center, gives a
block partition with `m < 2k` blocks whose total internal cost `A` equals the solution's cost. -/
theorem lemma_3_2 (V : Type u) [MetricSpace V] (z : ℝ) (hz : 1 ≤ z) (n k U : ℕ)
    (p : Fin n → V) (F : Set V) (hk : 0 < k) (hkn : k < n) (hU : 0 < U) (hnU : n ≤ k * U)
    (S : SoftSolution V n) (hS : IsUncapSolution F k S) (B : BlockPartition V n)
    (κ : Fin B.numBlocks → Fin S.numCenters)
    (hassign : ∀ q, S.assign q = κ (B.block q))
    (hrep : ∀ i, B.rep i = S.loc (κ i))
    (hne : ∀ i, (B.members i).Nonempty) (hsize : ∀ i, B.size i ≤ U)
    (hcount : ∀ j, (Finset.univ.filter fun i => κ i = j).card =
      ⌈(S.load j : ℝ) / (U : ℝ)⌉₊) :
    IsBlockPartition k U F B ∧ B.numBlocks < 2 * k ∧ B.totalCost z p = S.cost z p := by sorry

end ChengCapClustering.Soft
