-- Prove2me | Theorems.Thm_Brooks_colorable_of_max_deg_cliqueFree
-- name    : Brooks.colorable_of_max_deg_cliqueFree
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-19T06:06:45.510043+00:00
-- url     : https://prove2.me/theorems/f0af4fab-e46e-4c1f-9b9f-7c50500eaf7e
-- title:
--   Brooks' Theorem for k ≥ 3
-- statement:
--   **Brooks' Theorem ($k \ge 3$).** Let $G$ be a finite simple graph with maximum degree at most $k$, where $k \ge 3$. If $G$ contains no $(k+1)$-clique ($K_{k+1}$-free), then $G$ is properly $k$-vertex-colorable:
--
--   $$\Delta(G) \le k \;\wedge\; \omega(G) \le k \;\wedge\; k \ge 3 \quad\Longrightarrow\quad \chi(G) \le k.$$
-- source:
--   R. L. Brooks, On colouring the nodes of a network, Proc. Cambridge Philos. Soc. 37 (1941), 194–197; formalized via M. Zając, A short proof of Brooks' theorem, arXiv:1805.11176 (2018).

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Set.Card

universe u
namespace Brooks

theorem colorable_of_max_deg_cliqueFree
    {V : Type u} [Fintype V] (G : SimpleGraph V) {k : ℕ} (hk : 3 ≤ k)
    (hdeg : ∀ v : V, (G.neighborSet v).encard ≤ k)
    (hnoK : G.CliqueFree (k + 1)) :
    G.Colorable k := by sorry
end Brooks
