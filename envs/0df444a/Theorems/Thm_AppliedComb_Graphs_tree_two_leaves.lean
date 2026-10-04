-- Prove2me | Theorems.Thm_AppliedComb_Graphs_tree_two_leaves
-- name    : AppliedComb.Graphs.tree_two_leaves
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:01:14.756445+00:00
-- url     : https://prove2.me/theorems/4cf7622b-fc25-411c-8e5c-ce87cdcf90c0
-- title:
--   Proposition 5.11 — every tree on n ≥ 2 vertices has at least two leaves
-- statement:
--   Let $T = (V, E)$ be a tree (a connected graph containing no cycle) on $n = |V|$ vertices, and call a vertex $v$ a **leaf** if $\deg_T(v) = 1$. If $n \ge 2$, then
--   $$\bigl|\{v \in V : \deg_T(v) = 1\}\bigr| \ge 2.$$
--
--   This is the elementary fact behind induction on trees: removing a leaf from a tree leaves a tree.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 74, Proposition 5.11

import Mathlib
import Definitions.Def_AppliedComb_Graphs_IsCycle

namespace AppliedComb.Graphs

/-- Keller–Trotter, p. 74, Proposition 5.11. Every tree on `n ≥ 2` vertices has at least two
leaves, a leaf being a vertex of degree `1`. -/
theorem tree_two_leaves {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) (hn : Fintype.card V = n) (h2 : 2 ≤ n) (hT : IsTree G) :
    2 ≤ (Finset.univ.filter (fun v : V => G.degree v = 1)).card := by sorry

end AppliedComb.Graphs
