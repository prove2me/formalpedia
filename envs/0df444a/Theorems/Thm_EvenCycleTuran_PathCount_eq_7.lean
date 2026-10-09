-- Prove2me | Theorems.Thm_EvenCycleTuran_PathCount_eq_7
-- name    : EvenCycleTuran.PathCount.eq_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:27:33.482024+00:00
-- url     : https://prove2.me/theorems/2a12ad23-8d11-4c99-b2e1-47d2bc166a16
-- title:
--   Equation (7) — two walks for each path
-- statement:
--   Let $G$ be a graph on $n$ vertices and let $l\ge2$. Write $A$ for its adjacency matrix. The number of unlabelled $l$-vertex paths and the number of walks on $l$ vertices satisfy
--
--   $$
--   2\mathcal N(P_l,G)\le \sum_{i,j\in V(G)}(A^{l-1})_{ij}.
--   $$
--
--   The sum counts all walks of $l-1$ edges, including those that revisit vertices. This comparison connects the path count to the adjacency matrix.
--
--   **Formalization Note** No cycle-freeness assumption is needed for this inequality. The paper uses it inside a proof for a cycle-free graph.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 30, §7.1, equation (7)

import Mathlib
import Definitions.Def_EvenCycleTuran_PathCount_Setting

namespace EvenCycleTuran.PathCount

/-- Equation (7): every unlabelled path with at least two vertices gives two
oriented walks. -/
theorem eq_7 (n l : ℕ) (hl : 2 ≤ l) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] :
    2 * G.copyCount (SimpleGraph.pathGraph l) ≤
      ∑ i : Fin n, ∑ j : Fin n, ((G.adjMatrix ℕ) ^ (l - 1)) i j := by sorry

end EvenCycleTuran.PathCount
