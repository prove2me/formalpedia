-- Prove2me | Theorems.Thm_EvenCycleTuran_PathCount_rayleigh_step
-- name    : EvenCycleTuran.PathCount.rayleigh_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:27:34.585488+00:00
-- url     : https://prove2.me/theorems/4e047e2c-41a2-482b-bd6b-ab83bbfd19e3
-- title:
--   §7.1 — adjacency walk sum bounded by spectral radius
-- statement:
--   Let $G$ have $n$ vertices, real adjacency matrix $A$, and spectral radius $\mu(G)$. For every $l\ge1$,
--
--   $$
--   \sum_{i,j\in V(G)}(A^{l-1})_{ij}\le n\,\mu(G)^{l-1}.
--   $$
--
--   This bounds the total walk count by a graph-wide spectral quantity and is the matrix inequality used in both path-count upper bounds of the paper.
--
--   **Formalization Note** The spectral radius is the maximum of the absolute values of the real eigenvalues. The finite index set gives zero for the empty graph.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 30, §7.1, paragraph following equation (7)

import Mathlib
import Definitions.Def_EvenCycleTuran_PathCount_Setting

namespace EvenCycleTuran.PathCount

/-- The Rayleigh quotient bounds the all-ones quadratic form of a power of the
adjacency matrix by the graph's spectral radius. -/
theorem rayleigh_step (n l : ℕ) (hl : 1 ≤ l) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] :
    (∑ i : Fin n, ∑ j : Fin n, ((G.adjMatrix ℝ) ^ (l - 1)) i j) ≤
      (n : ℝ) * specRad G ^ (l - 1) := by sorry

end EvenCycleTuran.PathCount
