-- Prove2me | Theorems.Thm_DecrNearAddAPSP_W2_lemma_5_1
-- name    : DecrNearAddAPSP.W2.lemma_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T06:05:40.257196+00:00
-- url     : https://prove2.me/theorems/b807fd9f-1dc2-4efc-a703-a6caaf725b87
-- title:
--   Lemma 5.1 [BK06] — E_S preserves δ(u, v) when δ(u, v) < δ(u, p_S(u)), and E_S ∪ E(p_S(u)) preserves δ(u, p_S(u))
-- statement:
--   Let $G=(V,E,w)$ be a weighted graph with positive integer weights, $S\subseteq V$, and let $p_S(u)$ be a pivot of $u$: any $p\in S$ with $\delta(u,p)=\min_{s\in S}\delta(u,s)$. Let $E_S=\bigcup_{x}\{(x,y)\in E:w(x,y)<\delta(x,S)\}$ and $G_S=(V,E_S)$, and let $E(p)$ be the edges incident to $p$. Then:
--
--   1. for every $v\in V$ with $\delta(u,v)<\delta(u,p_S(u))$,
--   $$\delta_{G_S}(u,v)=\delta_G(u,v);$$
--   2. the distance between $u$ and $p_S(u)$ in $(V,E_S\cup E(p_S(u)))$ is $\delta_G(u,p_S(u))$.
--
--   This is the structural property of hierarchy-induced edge sets due to Baswana and Kavitha that the stretch analyses of §5 and §6 rest on: light paths survive in the sparse subgraph $E_S$.
--
--   Differences from the source:
--
--   - reading: a graph G = (V, E) (Lemma statement); §5 p. 25: "each edge e ∈ E has a positive weight w(e) > 0" → G.PosWeights (every edge weight ≥ 1); reason: standing assumption of the weighted sections (§5 p. 25), with integer weights (p. 6)
--   - encoding: vertex set V, distances δ → V = Fin n; δ in ℕ∞ (∞ = no path); reason: Lean convention; same instances
--   - reading: p_S(u) = arg min_{s∈S} δ(u, s) (breaking ties arbitrarily) → every p ∈ S with δ(u, p) ≤ δ(u, s) for all s ∈ S (the statement holds for each such choice); reason: ties are arbitrary on p. 6, so the lemma must hold for every minimizer
--   - encoding: "G_S preserves the exact distance between u and v" → δ_{(V, E_S)}(u, v) = δ_G(u, v), (V, F) keeping G's edges in F with G's weights; reason: the meaning of preserving a distance
-- source:
--   Koveshi, Roditty, Sapir, First Near-Additive All-Pairs Approximate Shortest Paths in Decremental Weighted Graphs, arXiv:2611.04635 (PDF sha256 6bb2b230…), p. 26, Lemma 5.1

import Mathlib
import Definitions.Def_DecrNearAddAPSP_W2_Graphs

namespace DecrNearAddAPSP.W2

/-- **Lemma 5.1** ([BK06], p. 26). Let `G` have positive edge weights, `S ⊆ V`, and let `p` be a
pivot of `u` in `S` (any minimizer of `δ(u, ·)` over `S`). (1) For every `v` with
`δ(u, v) < δ(u, p)`, the subgraph `G_S = (V, E_S)` has `δ_{G_S}(u, v) = δ_G(u, v)`. (2) The distance
between `u` and `p` in `(V, E_S ∪ E(p))` is `δ_G(u, p)`. -/
theorem lemma_5_1 {n : ℕ} (G : WGraph (Fin n)) (S : Finset (Fin n)) (u p : Fin n)
    (hpos : G.PosWeights) (hp : G.IsPivot S u p) :
    (∀ v : Fin n, G.dist u v < G.dist u p →
      (G.restrict (G.hierEdges S)).dist u v = G.dist u v) ∧
    (G.restrict (G.hierEdges S ∪ G.incident p)).dist u p = G.dist u p := by sorry

end DecrNearAddAPSP.W2
