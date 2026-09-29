-- Prove2me | Theorems.Thm_Conway99_srg_243_22_1_2
-- name    : Conway99.srg_243_22_1_2
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-06T16:14:32.668516+00:00
-- url     : https://prove2.me/theorems/7bdec294-1f68-40b5-af01-e31b30533469
-- title:
--   Berlekamp–van Lint–Seidel graph: existence at $(243,22,1,2)$
-- statement:
--   There exists a strongly regular graph with parameters $(243,22,1,2)$.
--
--   The Berlekamp–van Lint–Seidel graph is such a graph: its vertices are the $3^{11}/3^{6} = 243$ cosets of the perfect ternary Golay code $[11,6,5]_3$ in $\mathbb{F}_3^{11}$, with two cosets adjacent when their difference contains a vector of Hamming weight $1$. Equivalently it is the Cayley graph on $\mathbb{F}_3^{5}$ whose connection set consists of the $22$ syndromes $\pm h_i$ of the weight-one vectors, where $h_1, \dots, h_{11}$ are the columns of a parity check matrix of the code. It is the largest member of the family $\lambda = 1$, $\mu = 2$ known to exist, and the only known example that is not the trivial one on $9$ vertices.
-- source:
--   E. R. Berlekamp, J. H. van Lint, J. J. Seidel, 'A strongly regular graph derived from the perfect ternary Golay code', in: A Survey of Combinatorial Theory, North-Holland, 1973, pp. 25-30; see also https://en.wikipedia.org/wiki/Berlekamp%E2%80%93van_Lint%E2%80%93Seidel_graph

import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

open SimpleGraph

namespace Conway99

theorem srg_243_22_1_2 : ∃ (α : Type) (_ : Fintype α) (g : SimpleGraph α)
    (_ : DecidableRel g.Adj), IsSRGWith g 243 22 1 2 := by sorry

end Conway99
