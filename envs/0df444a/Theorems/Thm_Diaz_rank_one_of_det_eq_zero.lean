-- Prove2me | Theorems.Thm_Diaz_rank_one_of_det_eq_zero
-- name    : Diaz.rank_one_of_det_eq_zero
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T07:14:40.989546+00:00
-- url     : https://prove2.me/theorems/5b000721-8ba4-48ae-a670-e17a71c11596
-- title:
--   A singular $2\times2$ matrix is $(x_iy_j)$, and then $w^{\mathsf T}Mv=(w\cdot x)(v\cdot y)$
-- statement:
--   **A singular $2\times2$ matrix factors as $(x_i y_j)$, and its coefficients factor accordingly.**
--
--   Let $F$ be a field and $M$ a $2\times2$ matrix over $F$ with $\det M = 0$. Then there are
--   $p, q \in F^2$ with $M_{ij} = p_i q_j$ for all $i,j$, and for all $w, v \in F^2$
--
--   $$\sum_{i}\sum_{j} w_i M_{ij} v_j = \Bigl(\sum_i w_i p_i\Bigr)\Bigl(\sum_j q_j v_j\Bigr).$$
--
--   **Why.** A singular $2\times2$ matrix is either zero or of rank one, and in either case admits a
--   factorisation $M = pq^{\mathsf T}$; the coefficient identity is then immediate. The Lean proof
--   constructs $p$ and $q$ explicitly by cases on which entries vanish.
--
--   **Role.** This is the whole mechanism of Carlo Perassi's proposition that the augmented conjecture is
--   strong four exponentials. Once $M = (x_iy_j)$ one has $w^{\mathsf T} M v = (w \cdot x)(v \cdot y)$, so a
--   vanishing $\overline{\mathbb{Q}}$-coefficient exists exactly when $x_1,x_2$ or $y_1,y_2$ are
--   $\overline{\mathbb{Q}}$-linearly dependent — which is the contrapositive of the strong four exponentials
--   statement for the four products $x_iy_j$. That identifies the Dasgupta--Kakde Matrix Coefficient
--   Conjecture in dimension two, in its augmented form over $\widetilde{\mathcal L}$, with strong four
--   exponentials, and locates a Diaz candidate exactly: it violates the augmented conjecture, while saying
--   nothing about the conjecture as literally stated over $\mathrm{span}_{\overline{\mathbb{Q}}}\mathcal{L}$,
--   since the entry $r = |u|$ is a non-zero algebraic number.
--
--   The same factorisation gives the one-line proof, recorded in a remark of his, of the matrix-coefficient assertion for $H_u$,
--   which is the case $K=\overline{\mathbb{Q}}$ of Theorem 4.1 of his companion note to https://github.com/carlok/diaz-modulus-lean (version 1.9, 25 September 2026, GitHub release note-v1.9): $H_u = c d^{\mathsf T}$ with $c = (u, r)^{\mathsf T}$ and
--   $d = (r, \bar u)^{\mathsf T}$.
--
--   Source: Carlo Perassi, unpublished apart from this node: the proof of his proposition that the augmented conjecture is strong four exponentials, and his
--   remark on $H_u$. The linear algebra is classical;
--   no novelty is claimed.

import Mathlib

open ComplexConjugate

theorem Diaz.rank_one_of_det_eq_zero {F : Type*} [Field F] (M : Matrix (Fin 2) (Fin 2) F)
    (hM : M.det = 0) :
    ∃ p q : Fin 2 → F, (∀ i j, M i j = p i * q j) ∧
      ∀ w v : Fin 2 → F, ∑ i, ∑ j, w i * M i j * v j
        = (∑ i, w i * p i) * (∑ j, q j * v j) := by sorry
