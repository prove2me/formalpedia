-- Prove2me | Theorems.Thm_Balinski61_Connectivity_graph_n_tuply_connected
-- name    : Balinski61.Connectivity.graph_n_tuply_connected
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:51:03.212912+00:00
-- url     : https://prove2.me/theorems/dbeb9f07-5696-4aae-bc58-8eec3bddc656
-- title:
--   Balinski's THEOREM — the graph of a bounded full-dimensional polyhedron in n-space is n-tuply connected
-- statement:
--   Let $S=\{x\in\mathbb R^n:\langle a_i,x\rangle\le b_i,\ i=1,\dots,m\}$ be the polyhedral convex set of system (1), with Balinski's standing assumptions:
--
--   1. the only solution to $AX\le0$ is $X=0$;
--   2. there exists a solution $X^0$ which satisfies $AX^0<b$.
--
--   Let $G(S)$ be the graph whose points are the vertices of $S$ and whose lines are the edges of $S$. Then $G(S)$ is $n$-tuply connected: it has at least $n+1$ points, and for every set $X$ of at most $n-1$ vertices,
--   $$G(S)-X\ \text{is connected}.$$
--
--   This is Balinski's theorem (THEOREM, p. 432): "The vertices, considered as points, and the edges, considered as lines, of the convex polyhedral set $S$ form an $n$-tuply connected graph $G(S)$." Under the two assumptions $S$ is exactly a full-dimensional polytope in $\mathbb R^n$, so the theorem says that the graph of every $n$-dimensional polytope is vertex $n$-connected, a basic structural fact of polyhedral combinatorics.
--
--   **Formalization Note** $n$ is the dimension of the space and $m$ the number of inequalities. The definition of $n$-tuply connected is the paper's own ("at least $n+1$ points", "dropping out $n-1$ or fewer points"), not "exactly $n-1$" as in the first lines of the proof. Edges are the extreme segments of $S$ (`Hirsch.Adj`), not arbitrary pairs of vertices.
-- source:
--   Balinski, On the graph structure of convex polyhedra in n-space, Pacific J. Math. 11 (1961), p. 432, THEOREM

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Balinski61_Connectivity_Polyhedron
import Definitions.Def_Balinski61_Connectivity_TuplyConnected

open scoped RealInnerProductSpace

namespace Balinski61.Connectivity

theorem graph_n_tuply_connected (n m : ℕ)
    (a : Fin m → EuclideanSpace ℝ (Fin n)) (b : Fin m → ℝ)
    (hS : StandingAssumptions a b) :
    IsNTuplyConnected (polyGraph (Hirsch.Hpoly a b)) n := by sorry

end Balinski61.Connectivity
