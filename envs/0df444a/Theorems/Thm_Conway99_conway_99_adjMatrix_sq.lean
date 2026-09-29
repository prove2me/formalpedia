-- Prove2me | Theorems.Thm_Conway99_conway_99_adjMatrix_sq
-- name    : Conway99.conway_99_adjMatrix_sq
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-06T16:14:58.776359+00:00
-- url     : https://prove2.me/theorems/d8c4b23c-1eca-4ca6-b019-da0912e65d48
-- title:
--   Spectral identity: $A^2 + A = 12 I + 2 J$
-- statement:
--   Let $A$ be the adjacency matrix over $\mathbb{Z}$ of a strongly regular graph with parameters $(99,14,1,2)$, let $I$ be the identity matrix and let $J$ be the all-ones matrix. Then
--
--   $$A^2 + A = 12\,I + 2\,J .$$
--
--   This is the general strongly regular identity $A^2 = kI + \lambda A + \mu(J - I - A)$ with $(k,\lambda,\mu) = (14,1,2)$. Equivalently $(A - 3I)(A + 4I) = 2J$, which exhibits $3$ and $-4$ as the eigenvalues of $A$ on the space orthogonal to the all-ones vector; their multiplicities are $54$ and $44$. The identity is the entry point to every spectral argument about a hypothetical $99$-graph.
-- source:
--   Adjacency matrix identity for strongly regular graphs (cf. Mathlib SimpleGraph.IsSRGWith.matrix_eq), specialised to (99, 14, 1, 2); https://en.wikipedia.org/wiki/Strongly_regular_graph

import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Data.Matrix.Basic

open SimpleGraph

namespace Conway99

theorem conway_99_adjMatrix_sq {V : Type*} [Fintype V] [DecidableEq V]
    {g : SimpleGraph V} [DecidableRel g.Adj] (h : g.IsSRGWith 99 14 1 2) :
    (g.adjMatrix ℤ) ^ 2 + g.adjMatrix ℤ =
      12 • (1 : Matrix V V ℤ) + 2 • (Matrix.of fun _ _ => (1 : ℤ)) := by sorry

end Conway99
