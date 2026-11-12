-- Prove2me | Theorems.Thm_DecrNearAddAPSP_W2_lemma_6_4
-- name    : DecrNearAddAPSP.W2.lemma_6_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T06:05:32.638844+00:00
-- url     : https://prove2.me/theorems/a81d486f-1b23-49a8-bbb1-f9988a57a813
-- title:
--   Lemma 6.4 — G_{i+1}(u) = (V, E_{i+1} ∪ E(u)) preserves δ(u, v) for v ∈ C_G(u) and the cluster of u
-- statement:
--   Let $G$ be a weighted graph with positive integer weights, let $S_{i+1}\subseteq S_i\subseteq V$ be two consecutive levels of the hierarchy, $E_{i+1}=E_{S_{i+1}}=\bigcup_x\{(x,y)\in E:w(x,y)<\delta_G(x,S_{i+1})\}$, and for a vertex $u$ let $G_{i+1}(u)=(V,E_{i+1}\cup E(u))$ with $G$'s weights. For a graph $H$ let $C_H(u)=\{x\in V:\delta_H(x,u)<\delta_H(x,S_{i+1})\}$. For any $u\in S_i$ and $v\in C_G(u)$:
--
--   1. $\delta_G(u,v)=\delta_{G_{i+1}(u)}(u,v)$;
--   2. the clusters of $u$ with respect to $G$ and $G_{i+1}(u)$ are identical:
--   $$
--   C_{G_{i+1}(u)}(u)=C_G(u).
--   $$
--
--   The lemma lets the hopset construction of §6.3 grow the cluster trees of $u$ in the sparse graph $G_{i+1}(u)$ instead of $G$. Clause 2 is false as printed: with edges $u$–$v$ of weight $10$ and $v$–$s$ of weight $1$, $S_{i+1}=\{s\}$, $S_i=\{u,s\}$, the edge $v$–$s$ is not in $E_{i+1}$, so $v$ is cut off from $S_{i+1}$ in $G_{i+1}(u)$ and joins $u$'s cluster there but not in $G$ (take the lemma's $v$ to be $u$ itself). The statement is posed as printed.
--
--   Differences from the source:
--
--   - reading: a graph G = (V, E) (Lemma statement); §5 p. 25: "each edge e ∈ E has a positive weight w(e) > 0" → G.PosWeights (every edge weight ≥ 1); reason: standing assumption of the weighted sections (§5 p. 25), with integer weights (p. 6)
--   - reading: S_i, S_{i+1} levels of the hierarchy R(q, k) (Definition 2.1) → any two sets S_{i+1} ⊆ S_i ⊆ V; reason: the lemma is deterministic given the sample; nested pairs cover every outcome of R(q, k)
--   - reading: C_{G_{i+1}(u)}(u), the cluster with respect to G_{i+1}(u) → {x : δ_H(x, u) < δ_H(x, S_{i+1})} with both distances in H = G_{i+1}(u); reason: the cluster definition of p. 7 applied in the graph H, as the proof writes δ_{G_{i+1}(u)}(v, S_{i+1})
--   - reading: For any u ∈ S_i and v ∈ C_G(u), the subgraph satisfies 1. … 2. … → both clauses under both hypotheses u ∈ S_i and v ∈ C_G(u); reason: as printed
--   - encoding: vertex set V, distances δ → V = Fin n; δ in ℕ∞ (∞ = no path); reason: Lean convention; same instances
-- source:
--   Koveshi, Roditty, Sapir, First Near-Additive All-Pairs Approximate Shortest Paths in Decremental Weighted Graphs, arXiv:2611.04635 (PDF sha256 6bb2b230…), p. 43, Lemma 6.4

import Mathlib
import Definitions.Def_DecrNearAddAPSP_W2_Graphs

namespace DecrNearAddAPSP.W2

/-- **Lemma 6.4** (p. 43). Let `G` have positive weights, let `S_{i+1} ⊆ S_i ⊆ V` be two consecutive
levels of the hierarchy, `E_{i+1} = E_{S_{i+1}}`, and for `u ∈ S_i` let
`G_{i+1}(u) = (V, E_{i+1} ∪ E(u))`. For any `u ∈ S_i` and `v ∈ C_G(u)`: (1)
`δ_G(u, v) = δ_{G_{i+1}(u)}(u, v)`; (2) `C_{G_{i+1}(u)}(u) = C_G(u)`, where
`C_H(u) = {x : δ_H(x, u) < δ_H(x, S_{i+1})}`. -/
theorem lemma_6_4 {n : ℕ} (G : WGraph (Fin n)) (Si Si1 : Finset (Fin n)) (hpos : G.PosWeights)
    (hsub : Si1 ⊆ Si) (u v : Fin n) (hu : u ∈ Si) (hv : v ∈ G.cluster Si1 u) :
    G.dist u v = (G.restrict (G.hierEdges Si1 ∪ G.incident u)).dist u v ∧
    (G.restrict (G.hierEdges Si1 ∪ G.incident u)).cluster Si1 u = G.cluster Si1 u := by sorry

end DecrNearAddAPSP.W2
