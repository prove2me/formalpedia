-- Prove2me | Theorems.Thm_DecrNearAddAPSP_W2_section_6_1_rounding
-- name    : DecrNearAddAPSP.W2.section_6_1_rounding
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T06:05:35.521085+00:00
-- url     : https://prove2.me/theorems/3a17bb47-9bd3-468a-b6da-13d794068688
-- title:
--   §6.1 rounding bound — Bernstein's scaled graph G_i has positive integer weights and every ≤h-hop path of weight in [2^i, 2^{i+1}] has G_i-weight ≤ ⌈4h/ε⌉
-- statement:
--   Let $G$ be a weighted graph with positive integer weights, $0<\varepsilon<1$, $h\ge1$ an integer hop parameter, $i\ge0$ an integer, and $\alpha_i=\varepsilon\,2^i/h$. The scaled graph $G_i$ keeps the edges of weight at most $2^{i+1}$, rounds each kept weight up to the nearest integer multiple of $\alpha_i$ and divides by $\alpha_i$, so the edge $e$ gets weight $\lceil w(e)/\alpha_i\rceil$. Then:
--
--   1. every edge of $G_i$ has a positive integer weight: $\lceil w(e)/\alpha_i\rceil\ge1$ whenever $w(e)\le 2^{i+1}$;
--   2. for every path $p$ of $G$ (any walk, simple or not) with at most $h$ hops and $2^i\le w(p)\le 2^{i+1}$,
--   $$
--   w_{G_i}(p)=\sum_{e\in p}\Big\lceil\frac{w(e)}{\alpha_i}\Big\rceil\ \le\ \Big\lceil\frac{4h}{\varepsilon}\Big\rceil .
--   $$
--
--   This is what lets an ES-tree on $G_i$ run to depth $\lceil 4h/\varepsilon\rceil$ independently of $W_{\max}$ (Bernstein's rounding, used by SCALE in §7).
--
--   Differences from the source:
--
--   - reading: 0 < ε (the scaled graph is defined for the paper's ε) → 0 < ε < 1; reason: the standing range of the §6 tools (Theorem 7, Lemma B.2 p. 97); the bound fails for large ε, where h edges each rounded to 1 exceed ⌈4h/ε⌉
--   - generalization: for each 0 ≤ i ≤ log(nW_max) → for every i ∈ ℕ; reason: the claim holds for each scale separately; the paper's range is a subset, so the statement specializes to it
--   - encoding: every edge in G_i has a positive integer weight → 0 < ⌈w(e)/α_i⌉ in ℤ for every edge with w(e) ≤ 2^{i+1}; reason: the ceiling is an integer by type; the kept edges are those of weight ≤ 2^{i+1}
--   - generalization: any path p of at most h hops in G → every walk of G (simple or not) with at most h edges; reason: p. 6 defines a path as a sequence of edges; every edge of p has weight ≤ w(p) ≤ 2^{i+1} and is kept, and the statement specializes to simple paths
--   - reading: a graph G = (V, E) (Lemma statement); §5 p. 25: "each edge e ∈ E has a positive weight w(e) > 0" → G.PosWeights (every edge weight ≥ 1); reason: standing assumption of the weighted sections (§5 p. 25), with integer weights (p. 6)
-- source:
--   Koveshi, Roditty, Sapir, First Near-Additive All-Pairs Approximate Shortest Paths in Decremental Weighted Graphs, arXiv:2611.04635 (PDF sha256 6bb2b230…), p. 36, §6.1

import Mathlib
import Definitions.Def_DecrNearAddAPSP_W2_Graphs

namespace DecrNearAddAPSP.W2

/-- **§6.1 rounding bound** (p. 36). Let `G` have positive integer weights, `0 < ε < 1`, `h ≥ 1` a
hop parameter, `i ∈ ℕ`, and `α_i = ε·2^i/h`. In the scaled graph `G_i` (edges of weight at most
`2^{i+1}`, weight `w` mapped to `⌈w/α_i⌉`) every edge has a positive integer weight, and every path
`p` of `G` (any walk, simple or not) with at most `h` hops and `2^i ≤ w(p) ≤ 2^{i+1}` has `w_{G_i}(p) ≤ ⌈4h/ε⌉`. -/
theorem section_6_1_rounding {n : ℕ} (G : WGraph (Fin n)) (hpos : G.PosWeights) (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (h i : ℕ) (hh : 1 ≤ h) :
    (∀ e ∈ G.adj.edgeSet, G.wt e ≤ 2 ^ (i + 1) → 0 < scaledWeight ε h i (G.wt e)) ∧
    (∀ (u v : Fin n) (p : G.adj.Walk u v), p.length ≤ h →
      2 ^ i ≤ G.walkWeight p → G.walkWeight p ≤ 2 ^ (i + 1) →
      scaledWalkWeight G ε h i p ≤ ⌈4 * (h : ℝ) / ε⌉) := by sorry

end DecrNearAddAPSP.W2
