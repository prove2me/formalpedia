-- Prove2me | Theorems.Thm_AppliedComb_Ramsey_six_vertices
-- name    : AppliedComb.Ramsey.six_vertices
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:18:14.299654+00:00
-- url     : https://prove2.me/theorems/0b0c4dc0-e9bb-4ca8-ba4f-b0ae0d82a91a
-- title:
--   Lemma 11.1 — a graph on six vertices has a triangle or an independent 3-set
-- statement:
--   Let $G$ be a finite simple graph with at least six vertices. Then $G$ contains a complete subgraph on $3$ vertices (three pairwise adjacent vertices) or an independent set of size $3$ (three pairwise non-adjacent vertices):
--   $$|V(G)| \ge 6 \;\Longrightarrow\; \exists\, S \subseteq V(G),\ |S| = 3,\ S \text{ a clique or an independent set}.$$
--
--   This is the first case of Ramsey's theorem, $R(3, 3) \le 6$. The bound six is sharp: the cycle on five vertices has neither a triangle nor an independent set of size three.
--
--   **Formalization Note.** The graph is a Mathlib `SimpleGraph V` on a finite type `V : Type` with `6 ≤ Fintype.card V`; the two conclusions are `G.IsNClique 3 s` and `G.IsNIndepSet 3 s` for some `Finset` `s`.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 229, Lemma 11.1

import Mathlib

namespace AppliedComb.Ramsey

/-- Lemma 11.1, Keller & Trotter p. 229: every simple graph with six or more vertices contains a
complete subgraph on 3 vertices or an independent set of size 3. -/
theorem six_vertices (V : Type) [Fintype V] (hV : 6 ≤ Fintype.card V) (G : SimpleGraph V) :
    (∃ s : Finset V, G.IsNClique 3 s) ∨ (∃ s : Finset V, G.IsNIndepSet 3 s) := by sorry

end AppliedComb.Ramsey
