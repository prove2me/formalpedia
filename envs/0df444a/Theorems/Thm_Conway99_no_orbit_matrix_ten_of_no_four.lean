-- Prove2me | Theorems.Thm_Conway99_no_orbit_matrix_ten_of_no_four
-- name    : Conway99.no_orbit_matrix_ten_of_no_four
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-07T13:35:22.432708+00:00
-- url     : https://prove2.me/theorems/45b537fd-4e72-4cfa-8ec3-26c448c45d47
-- title:
--   No trace-$10$ orbit matrix with diagonal in $\{0,2\}$
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
--   **Claim.** No orbit matrix has trace $10$ with every diagonal entry in $\{0,2\}$:
--
--   $$\sum_{i=1}^{9}c_{ii}=10\ \text{ and }\ c_{ii}\ne 4\ \text{for all }i\ \Longrightarrow\ \text{no such }C\text{ exists}.$$
--
--   Under the hypothesis exactly five diagonal entries equal $2$ and four equal $0$. This is the residual case of Wilbrink's Theorem 5, and the one with no short argument on record: in the original paper the configurations that survive the hand analysis are eliminated by an exhaustive search reported as six hours on a programmable pocket calculator. The statement is therefore known to be true, but a machine-checkable proof still has to be produced, either by finding a structural argument or by arranging the search so that a proof assistant's kernel can carry it out.
-- source:
--   H. A. Wilbrink, 'On the (99,14,1,2) strongly regular graph', in: Papers dedicated to J. J. Seidel, EUT Report 84-WSK-03, Eindhoven University of Technology, 1984, pp. 342-355, https://pure.tue.nl/ws/files/2449333/256699.pdf ; Theorem 5, pp. 350-354. Decomposition of Conway99.no_orbit_matrix_of_diag_mem.

import Mathlib.Data.Matrix.Basic

namespace Conway99

theorem no_orbit_matrix_ten_of_no_four
    (C : Matrix (Fin 9) (Fin 9) ℕ) (hsymm : ∀ i j, C i j = C j i)
    (hrow : ∀ i, ∑ j, C i j = 14)
    (hsq : ∀ i j, (∑ k, C i k * C k j) + C i j = (if i = j then 12 else 0) + 22)
    (hdiag : ∀ i, C i i = 0 ∨ C i i = 2 ∨ C i i = 4)
    (htr : (∑ i, C i i) = 10)
    (hfour : ∀ i, C i i ≠ 4) : False := by sorry

end Conway99
