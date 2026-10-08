-- Prove2me | Theorems.Thm_ChinesePostman_Polyhedron_postman_polyhedron
-- name    : ChinesePostman.Polyhedron.postman_polyhedron
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:39:37.04502+00:00
-- url     : https://prove2.me/theorems/a437049b-0599-4adf-ae56-69fb200c9030
-- title:
--   §3, p. 93 — the convex hull of nonnegative integer solutions of (3.6) is the polyhedron of (3.2) and (3.5)
-- statement:
--   Let $G$ be a finite graph with node set $N$ and edge set $E$, where parallel edges are allowed and each edge meets two different nodes. Let $b_n\in\{0,1\}$ be the parity of the degree of node $n$; $n$ is an odd node when $b_n=1$. An edge meets a set $S\subseteq N$ when exactly one of its ends lies in $S$, and $S$ is an odd set when it contains an odd number of odd nodes.
--
--   Let $X\subseteq\mathbb R^E$ be the set of vectors $x$ with
--   $$x_e\in\mathbb Z,\quad x_e\ge 0\ (e\in E),\qquad \sum_{e\in E}a_{ne}x_e\equiv b_n\pmod 2\ (n\in N),$$
--   ((3.1), (3.2), (3.6)), and let $P\subseteq\mathbb R^E$ be the polyhedron
--   $$P=\Big\{x : x_e\ge 0\ (e\in E),\ \ \sum\{x_e : e\text{ meets }S\}\ge 1\ \text{ for every odd set } S\Big\}$$
--   ((3.2), (3.5)). Then
--   $$\operatorname{conv} X = P .$$
--
--   Both inclusions are asserted, and the equality is of subsets of $\mathbb R^E$; in particular the convex hull of $X$ is already closed. The vectors in $X$ are the numbers of extra traversals of the edges in postman tours, so the theorem describes the Chinese postman problem as a linear program.
--
--   **Formalization Note** The odd sets range over all subsets $S\subseteq N$ with an odd number of odd nodes, with no nonemptiness or properness restriction (both are automatic). Points of $X$ are real images of integer vectors.
-- source:
--   Edmonds and Johnson, Matching, Euler tours and the Chinese postman, Math. Programming 5 (1973), p. 93 (statement), p. 94 (restated), pp. 94–96 (proof), §3, (3.2), (3.5), (3.6)

import Mathlib
import Definitions.Def_ChinesePostman_Polyhedron_Setting

namespace ChinesePostman.Polyhedron

theorem postman_polyhedron {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) :
    convexHull ℝ (parityPoints G) = postmanPolyhedron G := by sorry

end ChinesePostman.Polyhedron
