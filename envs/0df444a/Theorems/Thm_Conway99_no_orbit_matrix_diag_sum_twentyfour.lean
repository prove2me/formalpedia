-- Prove2me | Theorems.Thm_Conway99_no_orbit_matrix_diag_sum_twentyfour
-- name    : Conway99.no_orbit_matrix_diag_sum_twentyfour
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-07T13:12:57.786737+00:00
-- url     : https://prove2.me/theorems/749b4e6f-7f4b-4f0f-8724-bba70691b9d3
-- title:
--   No orbit matrix with trace $24$
-- statement:
--   Call a $9\times9$ matrix $C=(c_{ij})$ with entries in $\mathbb{N}$ an **orbit matrix** if
--
--   $$C=C^{\mathsf T},\qquad \sum_{j=1}^{9}c_{ij}=14\ \ (1\le i\le 9),\qquad C^{2}+C=12\,I_9+22\,J_9,\qquad c_{ii}\in\{0,2,4\},$$
--
--   where $I_9$ is the identity and $J_9$ the all-ones matrix.
--
--   The name comes from the setting. Let $G$ be a strongly regular graph with parameters $(n,k,\lambda,\mu)=(99,14,1,2)$, whose existence is a long-standing open question. Its adjacency matrix satisfies $A^{2}+A=12I_{99}+2J_{99}$. An automorphism of $G$ of prime order $p>7$ has no fixed point, so $p\mid 99$ and $p=11$; such an automorphism would partition the $99$ vertices into nine orbits of size $11$, and the matrix $C$ counting how many neighbours in orbit $j$ a vertex of orbit $i$ has is symmetric, has constant row sums $k=14$, and inherits $C^{2}+C=12I_9+22J_9$ from $A$. That no orbit matrix exists is Wilbrink's Theorem 5, and it is what shows a $(99,14,1,2)$ graph cannot have an automorphism of order $11$, hence cannot be vertex-transitive.
--
--   *Formalization note.* The diagonal restriction $c_{ii}\in\{0,2,4\}$ is a consequence of the other three conditions rather than an extra assumption; it is carried explicitly because it cuts the search space. In the Lean statement $12I_9+22J_9$ is written entrywise as `(if i = j then 12 else 0) + 22`.
--
--   **Claim.** No orbit matrix has trace $24$:
--
--   $$\sum_{i=1}^{9}c_{ii}=24\ \Longrightarrow\ \text{no such }C\text{ exists}.$$
--
--   Together with the companion statement for trace $10$ and the fact that the trace can only be $10$ or $24$, this is one of the two branches into which Wilbrink's Theorem 5 splits. It is the shorter of the two: a trace of $24$ is large enough to force several diagonal entries to take their maximal value $4$, and rows with $c_{ii}=4$ are the most tightly constrained rows an orbit matrix can have.
-- source:
--   H. A. Wilbrink, 'On the (99,14,1,2) strongly regular graph', in: Papers dedicated to J. J. Seidel, EUT Report 84-WSK-03, Eindhoven University of Technology, 1984, pp. 342-355, https://pure.tue.nl/ws/files/2449333/256699.pdf ; Theorem 5, pp. 350-354. Decomposition of Conway99.no_orbit_matrix_of_diag_mem.

import Mathlib.Data.Matrix.Basic

namespace Conway99

theorem no_orbit_matrix_diag_sum_twentyfour
    (C : Matrix (Fin 9) (Fin 9) ℕ) (hsymm : ∀ i j, C i j = C j i)
    (hrow : ∀ i, ∑ j, C i j = 14)
    (hsq : ∀ i j, (∑ k, C i k * C k j) + C i j = (if i = j then 12 else 0) + 22)
    (hdiag : ∀ i, C i i = 0 ∨ C i i = 2 ∨ C i i = 4)
    (htr : (∑ i, C i i) = 24) : False := by sorry

end Conway99
