-- Prove2me | Theorems.Thm_Conway99_no_orbit_matrix_of_diag_mem
-- name    : Conway99.no_orbit_matrix_of_diag_mem
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-06T21:55:37.786261+00:00
-- url     : https://prove2.me/theorems/55b15ce2-5872-43b5-adae-fbd79544d119
-- title:
--   Wilbrink's orbit matrix with diagonal entries restricted to $\{0,2,4\}$
-- statement:
--   **Wilbrink's orbit matrix, with the diagonal already classified.**
--
--   There is no $9\times9$ matrix $C=(c_{ij})$ over $\mathbb{N}$ that is symmetric, has every row summing to $14$, satisfies $C^{2}+C=12I_9+22J_9$, **and** has every diagonal entry equal to $0$, $2$ or $4$.
--
--   This is `Conway99.conway_99_no_orbit_matrix` with the last condition added. That condition is not an extra assumption in any real sense — it is forced by the other three, and the companion reduction proves exactly that. Its purpose is to cut the search: without it a diagonal entry could a priori be anything up to $14$, and there are $15^{9}$ diagonals to consider; with it there are $3^{9}$, a factor of about $2600$ smaller, and each of the three values pins down the row it sits in very tightly.
--
--   **How the constraint arises.** The diagonal case $i=j$ of the matrix identity reads
--   $$\sum_{k=1}^{9} c_{ik}^{2} + c_{ii} = 34 .$$
--   Squaring preserves parity termwise, so $\sum_k c_{ik}^2 \equiv \sum_k c_{ik} = 14 \equiv 0 \pmod 2$, and therefore $c_{ii}$ is even. Separating the diagonal term and applying Cauchy–Schwarz to the eight off-diagonal entries of the row, which sum to $14-c_{ii}$ and whose squares sum to $34-c_{ii}-c_{ii}^{2}$, gives
--   $$(14-c_{ii})^{2} \;\le\; 8\left(34-c_{ii}-c_{ii}^{2}\right),$$
--   that is $9c_{ii}^{2}-20c_{ii}-76\le 0$, so $c_{ii}\le 4$.
--
--   **What is left.** The three admissible diagonal values are each rigid. If $c_{ii}=4$ the eight off-diagonal entries of row $i$ sum to $10$ with squares summing to $14$, which is exactly the minimum possible, so that row is $\{2,2,1,1,1,1,1,1\}$ up to order and nothing else. The values $0$ and $2$ leave a little more freedom. Combining that rigidity with the off-diagonal equations $\sum_k c_{ik}c_{jk} = 22 - c_{ij}$ is what remains, and it is the content of Wilbrink's Theorem 5.
-- source:
--   H. A. Wilbrink, 'On the (99,14,1,2) strongly regular graph', in: Papers dedicated to J. J. Seidel, EUT Report 84-WSK-03, Eindhoven University of Technology, 1984, pp. 342-355, https://pure.tue.nl/ws/files/2449333/256699.pdf ; Theorem 5, pp. 350-354. This is the statement of Conway99.conway_99_no_orbit_matrix with the diagonal classification (forced by the other hypotheses) added as an explicit assumption.

import Mathlib.Data.Matrix.Basic

namespace Conway99

theorem no_orbit_matrix_of_diag_mem :
    ¬ ∃ C : Matrix (Fin 9) (Fin 9) ℕ, (∀ i j, C i j = C j i) ∧ (∀ i, ∑ j, C i j = 14) ∧
      (∀ i j, (∑ k, C i k * C k j) + C i j = (if i = j then 12 else 0) + 22) ∧
      (∀ i, C i i = 0 ∨ C i i = 2 ∨ C i i = 4) := by sorry

end Conway99
