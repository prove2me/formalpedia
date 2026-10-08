-- Prove2me | Theorems.Thm_ChinesePostman_Polyhedron_postman_polyhedron_w
-- name    : ChinesePostman.Polyhedron.postman_polyhedron_w
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:39:25.915197+00:00
-- url     : https://prove2.me/theorems/de87a74c-f419-43a6-a094-89b9572efb08
-- title:
--   §3, p. 91 — the Chinese postman polyhedron (3.2), (3.2′), (3.3), (3.5) is the convex hull of its integer points
-- statement:
--   Let $G$ be a finite graph (parallel edges allowed, no loops) with node set $N$, edge set $E$, and $b_n\in\{0,1\}$ the parity of the degree of node $n$. Consider pairs $(x,w)\in\mathbb R^E\times\mathbb R^N$. Let $Y$ be the set of integer pairs satisfying
--   $$x_e\ge 0,\quad w_n\ge 0,\quad \sum_{e\in E}a_{ne}x_e-2w_n=b_n\ (n\in N)$$
--   ((3.1), (3.1′), (3.2), (3.2′), (3.3)), and let $Q$ be the **Chinese postman polyhedron**, the set of real pairs satisfying (3.2), (3.2′), (3.3) and the blossom inequalities
--   $$\sum\{x_e : e\text{ meets }S\}\ge 1\qquad\text{for every odd set } S. \tag{3.5}$$
--   Then
--   $$\operatorname{conv} Y = Q .$$
--
--   This is the form in which the polyhedron theorem is announced on p. 91, as a special case of the matching polyhedron theorem; the main theorem of the mission is its sharpening in the variables $x$ alone.
-- source:
--   Edmonds and Johnson, Matching, Euler tours and the Chinese postman, Math. Programming 5 (1973), p. 91, §3, (3.1)–(3.3), (3.5)

import Mathlib
import Definitions.Def_ChinesePostman_Polyhedron_Setting

namespace ChinesePostman.Polyhedron

theorem postman_polyhedron_w {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) :
    convexHull ℝ (wParityPoints G) = wPostmanPolyhedron G := by sorry

end ChinesePostman.Polyhedron
