-- Prove2me | Theorems.Thm_FarhiQAOA_Cubic_edge_type_count
-- name    : FarhiQAOA.Cubic.edge_type_count
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:30:50.034663+00:00
-- url     : https://prove2.me/theorems/51515f62-809c-47a6-a99d-e151b0ffd753
-- title:
--   Section V, pp. 8–9 — S edges of type g₄ and 4S + 3T edges of type g₅
-- statement:
--   Let $G$ be a connected 3-regular graph on $n \neq 4$ vertices with $S$ crossed squares and $T$ isolated triangles. Classify each edge $\langle jk\rangle$ by the number of common neighbours of $j$ and $k$, which is its subgraph type in figure (18). Then
--   $$\#\{\text{edges of type } g_4\} = S, \qquad \#\{\text{edges of type } g_5\} = 4S + 3T,$$
--   where type $g_4$ means two common neighbours and type $g_5$ means one.
--
--   Each crossed square contributes its diagonal as an edge of type $g_4$ and its four sides as edges of type $g_5$, and each isolated triangle contributes its three edges as edges of type $g_5$. Together with the edge count $3n/2$ this gives the coefficients of (32).
--
--   **Formalization Note** Edges are counted once, as ordered pairs $u<v$. The hypotheses "connected" and $n\neq 4$ exclude $K_4$, the paper's special case ("the only case where the analysis below does not apply", p. 8): in $K_4$ all six edges have two common neighbours while $S=T=0$.
-- source:
--   Farhi, Goldstone, Gutmann, A Quantum Approximate Optimization Algorithm, arXiv:1411.4028v1, pp. 8–9, Section V, between (31) and (32)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Adiabatic
import Definitions.Def_FarhiQAOA_Cubic_Types

namespace FarhiQAOA.Cubic

open QAlgorithms

/-- Farhi–Goldstone–Gutmann, Section V, pp. 8–9: in a connected 3-regular graph other than `K₄`
(`n ≠ 4`), the edges of subgraph type `g₄` (endpoints with 2 common neighbours) number `S`, and the
edges of type `g₅` (endpoints with 1 common neighbour) number `4S + 3T`. Edges are counted once,
as ordered pairs `u < v`. -/
theorem edge_type_count {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3) (hconn : G.Connected) (hn4 : n ≠ 4) :
    ((Finset.univ ×ˢ Finset.univ).filter fun e : Fin n × Fin n =>
        e.1 < e.2 ∧ G.Adj e.1 e.2 ∧ commonNbrCount G e.1 e.2 = 2).card = S G ∧
      ((Finset.univ ×ˢ Finset.univ).filter fun e : Fin n × Fin n =>
        e.1 < e.2 ∧ G.Adj e.1 e.2 ∧ commonNbrCount G e.1 e.2 = 1).card = 4 * S G + 3 * T G := by sorry

end FarhiQAOA.Cubic
