-- Prove2me | Theorems.Thm_Conway99_conway_99_orbit_matrix_exists
-- name    : Conway99.conway_99_orbit_matrix_exists
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-06T18:31:41.10604+00:00
-- url     : https://prove2.me/theorems/76eb99c9-cde9-4b36-914e-99a70fe96a17
-- title:
--   Orbit matrix of an order-$11$ automorphism of a $(99,14,1,2)$ graph
-- statement:
--   Let $G$ be a strongly regular graph with parameters $(99,14,1,2)$ and let $\sigma$ be a fixed-point-free automorphism of $G$ of order $11$. The cyclic group $\langle\sigma\rangle$ then partitions the vertex set into $9$ orbits $\Omega_1,\dots,\Omega_9$, each of length $11$.
--
--   For a vertex $x\in\Omega_i$ the number of neighbours of $x$ lying in $\Omega_j$ does not depend on the choice of $x$; call it $c_{ij}$. The resulting orbit matrix $C=(c_{ij})\in\mathbb{N}^{9\times 9}$ is symmetric, has constant row sums
--
--   $$\sum_{j=1}^{9} c_{ij}=k=14 ,$$
--
--   and satisfies the quadratic relation obtained from $A^2+(\mu-\lambda)A+(\mu-k)I=\mu J$ for the adjacency matrix $A$ of $G$, namely
--
--   $$C^{2}+C=12\,I_9+22\,J_9 ,$$
--
--   where $I_9$ is the identity matrix and $J_9$ the all-ones matrix of size $9$.
--
--   The theorem asserts that such a matrix exists. Orbit matrices reduce questions about a hypothetical graph on $99$ vertices to questions about a $9\times 9$ integer matrix, and are the standard tool for excluding prescribed automorphism groups of strongly regular graphs.
--
--   **Formalization Note** The conclusion is stated entrywise: symmetry as $c_{ij}=c_{ji}$, the row sums as $\sum_j c_{ij}=14$, and the matrix identity as $\sum_k c_{ik}c_{kj}+c_{ij}=12\,[i=j]+22$, which avoids subtraction in $\mathbb{N}$. Only the existence of a matrix with these three properties is asserted, which is what the exclusion argument uses.
-- source:
--   H. A. Wilbrink, 'On the (99,14,1,2) strongly regular graph', in: Papers dedicated to J. J. Seidel (P. J. de Doelder, J. de Graaf, J. H. van Lint, eds.), EUT Report 84-WSK-03, Eindhoven University of Technology, 1984, pp. 342-355, https://pure.tue.nl/ws/files/2449333/256699.pdf ; Theorem 4, pp. 346-348, applied in Section 3, pp. 350-351

import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Algebra.Order.Group.End
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Matrix.Basic

open SimpleGraph

namespace Conway99

theorem conway_99_orbit_matrix_exists {V : Type*} [Fintype V] {g : SimpleGraph V}
    [DecidableRel g.Adj] (h : g.IsSRGWith 99 14 1 2) (σ : g ≃g g) (hσ : orderOf σ = 11)
    (hfix : ∀ v : V, σ v ≠ v) :
    ∃ C : Matrix (Fin 9) (Fin 9) ℕ, (∀ i j, C i j = C j i) ∧ (∀ i, ∑ j, C i j = 14) ∧
      ∀ i j, (∑ k, C i k * C k j) + C i j = (if i = j then 12 else 0) + 22 := by sorry

end Conway99
