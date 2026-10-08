-- Prove2me | Theorems.Thm_ChinesePostman_Polyhedron_convexHull_parityPoints_subset
-- name    : ChinesePostman.Polyhedron.convexHull_parityPoints_subset
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:38:40.600522+00:00
-- url     : https://prove2.me/theorems/7e3912ee-4ba0-4315-b2df-c5818898c955
-- title:
--   §3, p. 95 — the polyhedron of (3.2) and (3.5) contains the convex hull of the parity points
-- statement:
--   Let $G$ be a finite graph (parallel edges allowed, no loops). Let $X\subseteq\mathbb R^E$ be the set of parity points, the vectors $x$ with $x_e\in\mathbb Z$, $x_e\ge 0$ and $\sum_e a_{ne}x_e\equiv b_n \pmod 2$ for every node $n$ ((3.1), (3.2), (3.6)), and let $P\subseteq\mathbb R^E$ be the postman polyhedron, the solutions of $x_e\ge 0$ and $\sum\{x_e: e\text{ meets }S\}\ge 1$ for every odd set $S$ ((3.2), (3.5)). Then
--   $$\operatorname{conv} X\subseteq P .$$
--   In particular $X\subseteq P$: every parity point satisfies the blossom inequalities.
--
--   This is the easy inclusion of the polyhedron theorem of §3.
-- source:
--   Edmonds and Johnson, Matching, Euler tours and the Chinese postman, Math. Programming 5 (1973), p. 95, §3, after (3.13)

import Mathlib
import Definitions.Def_ChinesePostman_Polyhedron_Setting

namespace ChinesePostman.Polyhedron

theorem convexHull_parityPoints_subset {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) :
    convexHull ℝ (parityPoints G) ⊆ postmanPolyhedron G := by sorry

end ChinesePostman.Polyhedron
