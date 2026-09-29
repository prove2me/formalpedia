-- Prove2me | Theorems.Thm_Conway99_conway_99_no_orbit_matrix
-- name    : Conway99.conway_99_no_orbit_matrix
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-06T18:31:40.688215+00:00
-- url     : https://prove2.me/theorems/bc80cca9-92c0-4ba4-99ad-dabaf2bd7c84
-- title:
--   Wilbrink (Theorem 5): the orbit matrix of an order-$11$ automorphism of a $(99,14,1,2)$ graph does not exist
-- statement:
--   There is no $9\times 9$ matrix $C=(c_{ij})$ with entries in $\mathbb{N}$ such that
--
--   1. $C$ is symmetric, $c_{ij}=c_{ji}$;
--   2. every row sums to $14$, $\sum_{j=1}^{9}c_{ij}=14$;
--   3. $C^{2}+C=12\,I_9+22\,J_9$, where $I_9$ is the identity and $J_9$ the all-ones matrix.
--
--   Equivalently, writing the third condition entrywise, there are no nonnegative integers $c_{ij}$ with
--
--   $$\sum_{k=1}^{9}c_{ik}^{2}=34-c_{ii},\qquad \sum_{k=1}^{9}c_{ik}c_{jk}=22-c_{ij}\ (i\neq j),\qquad \sum_{j=1}^{9}c_{ij}=14 .$$
--
--   These are exactly the conditions satisfied by the orbit matrix of an automorphism of order $11$ of a strongly regular graph with parameters $(99,14,1,2)$, whose $9$ orbits all have length $11$. The statement is a purely finite arithmetic assertion about $9\times9$ integer matrices, and it is the combinatorial core of Wilbrink's theorem that a $(99,14,1,2)$ graph admits no automorphism of order $11$.
--
--   **Formalization Note** The matrix identity is stated entrywise as $\sum_k c_{ik}c_{kj}+c_{ij}=12\,[i=j]+22$ to avoid subtraction in $\mathbb{N}$.
-- source:
--   H. A. Wilbrink, 'On the (99,14,1,2) strongly regular graph', in: Papers dedicated to J. J. Seidel (P. J. de Doelder, J. de Graaf, J. H. van Lint, eds.), EUT Report 84-WSK-03, Eindhoven University of Technology, 1984, pp. 342-355, https://pure.tue.nl/ws/files/2449333/256699.pdf ; Theorem 5, pp. 350-354

import Mathlib.Data.Matrix.Basic

namespace Conway99

theorem conway_99_no_orbit_matrix :
    ¬ ∃ C : Matrix (Fin 9) (Fin 9) ℕ, (∀ i j, C i j = C j i) ∧ (∀ i, ∑ j, C i j = 14) ∧
      ∀ i j, (∑ k, C i k * C k j) + C i j = (if i = j then 12 else 0) + 22 := by sorry

end Conway99
