-- Prove2me | Theorems.Thm_DynMaxMatchEC_Main_claim_3_13
-- name    : DynMaxMatchEC.Main.claim_3_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:03:30.629437+00:00
-- url     : https://prove2.me/theorems/83128a53-5b00-44db-a7e4-5f8e613089d5
-- title:
--   Claim 3.13 — at most 4n long and at most ρxn terrible paths in the multiset P of components of M∗ ∪ M_i
-- statement:
--   Let $G$ be a graph on $n$ vertices, $M_1,\dots,M_{z+x}$ pairwise disjoint matchings of $G$ with union $M$, $M^*$ a matching of $G$, $x\le z$ and $\rho\ge1$, such that $m(v)\le z$ for every vertex and $m(v)\ge z-(\rho-1)x$ for every $v\in S$, where $m(v)$ counts the edges of $M$ at $v$. Let $\mathcal P$ be the multiset of the paths $P_i(v)$ over all pairs $(i,v)$ for which $P_i(v)$ is defined. Then
--   $$\#\{P\in\mathcal P: P\text{ long}\}\le4n,\qquad\#\{P\in\mathcal P: P\text{ terrible}\}\le\rho xn.$$
--   This counting bound drives both the randomized procedures (Claims 3.16, 3.19) and the deterministic one (Claim 3.23).
--
--   Differences from the source:
--   - generalization: the state of the algorithm of §3.2 (subgraph system, z′-edge-coloring of G′, maximal matching M∗) → any graph with pairwise disjoint matchings M₁, …, M_{z+x} ⊆ E(G), a matching M∗ ⊆ E(G), x ≤ z, ρ ≥ 1, m(v) ≤ z for all v and m(v) ≥ z − (ρ − 1)x on S; reason: these are exactly the facts the proof uses (P1, the choice of c on p. 25, z′ = z + x ≤ 2z); every state of the algorithm satisfies them
--   - generalization: ρ = c log n for a large enough constant c → any real ρ ≥ 1; reason: the claim and its proof use only ρ ≥ 1 and the bound on m(v) on S
--   - encoding: the multiset P = ⋃ᵢ Pᵢ (every path appears once for each endpoint); I = {1, …, z′} → paths counted by the pairs (i, v) ∈ Fin (z + x) × Fin n with P_i(v) defined; reason: the multiset is indexed by these pairs; 0-based indices
-- source:
--   Chuzhoy, New Algorithms for Dynamic Maximal Matching and Edge Coloring (manuscript, Nov. 1, 2026; PDF sha256 2c277528…4ca5), p. 30, Claim 3.13 (setting: pp. 25–30, §3.2)

import Mathlib
import Definitions.Def_DynMaxMatchEC_Main_Model
import Definitions.Def_DynMaxMatchEC_Main_PathState

open Classical

namespace DynMaxMatchEC.Main

/-- **Claim 3.13** (Chuzhoy, manuscript Nov. 1, 2026, PDF sha256 2c277528…4ca5, p. 30). Let
`M_1, …, M_{z+x}` be pairwise disjoint matchings of `G` (the color classes of `M`), `M∗` a matching
of `G`, `x ≤ z`, `ρ ≥ 1`, `m(v) ≤ z` for every vertex and `m(v) ≥ z − (ρ − 1)x` for `v ∈ S`. Counting
the paths `P_i(v)` of the multiset `P` by their pairs `(i, v)`: at most `4n` are long (at least `z`
edges) and at most `ρxn` are terrible. -/
theorem claim_3_13 (n z x : ℕ) (σ : MState n (z + x)) (ρ : ℝ)
    (hcolG : ∀ i, ∀ e ∈ σ.col i, e ∈ σ.G.edgeSet) (hstarG : ∀ e ∈ σ.Mstar, e ∈ σ.G.edgeSet)
    (hcol : ∀ i, IsMatching (σ.col i)) (hdisj : ∀ i j, i ≠ j → Disjoint (σ.col i) (σ.col j))
    (hstar : IsMatching σ.Mstar) (hxz : x ≤ z) (hρ : 1 ≤ ρ)
    (hP1 : ∀ v, mdeg σ.Mall v ≤ z)
    (hS : ∀ v ∈ σ.S, (z : ℝ) - (ρ - 1) * x ≤ mdeg σ.Mall v) :
    (Finset.univ.filter fun q : Fin (z + x) × Fin n =>
        σ.PathDefined q.1 q.2 ∧ σ.IsLong z q.1 q.2).card ≤ 4 * n ∧
      ((Finset.univ.filter fun q : Fin (z + x) × Fin n =>
        σ.PathDefined q.1 q.2 ∧ σ.IsTerrible q.1 q.2).card : ℝ) ≤ ρ * x * n := by sorry

end DynMaxMatchEC.Main
