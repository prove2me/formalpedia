-- Prove2me | Theorems.Thm_DiazModulus_det_zero_linear_forms_rank_one_field
-- name    : DiazModulus.det_zero_linear_forms_rank_one_field
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T04:56:42.955041+00:00
-- url     : https://prove2.me/theorems/a0aa346e-4db7-4cac-a8fe-dcef38c9d02d
-- title:
--   Over a field of characteristic zero, a 2×2 matrix of linear forms with identically vanishing determinant has dependent rows or columns
-- statement:
--   **The linear-forms lemma over any field of characteristic zero.**
--
--   Let $F$ be a field of characteristic zero, and let $L$ be a $2\times2$ matrix of linear forms in $n$ variables over $F$, the entry $L_{ij}$ having coefficient vector $A_{ij} \in F^{n}$. If $\det L = L_{00}L_{11} - L_{01}L_{10}$ vanishes as a polynomial (the hypothesis lists its coefficients), then the rows of $L$ are $F$-linearly dependent or its columns are.
--
--   This extends `DiazModulus.det_zero_linear_forms_rank_one` from $\mathbb{Q}$ to any field of characteristic zero, with the same coordinate proof. It is used over $\overline{\mathbb{Q}}$.
--
--   **Novelty.** None claimed. Classical.
-- source:
--   Used over the algebraic numbers in the proofs of Theorems 5.4(c) and 5.6(b), (c) of Carlo Perassi, companion note to https://github.com/carlok/diaz-modulus-lean, version 1.9, 25 September 2026 (GitHub release note-v1.9), as the lemma on linear forms over a field of characteristic zero. Formal proof: Diaz modulus mission, 24 September 2026 (C. Perassi). Background: the classical description of linear spaces of rank-one matrices.

import Mathlib

namespace DiazModulus

theorem det_zero_linear_forms_rank_one_field {F : Type*} [Field F] [CharZero F] (n : ℕ)
    (A : Fin 2 → Fin 2 → Fin n → F)
    (hdet : ∀ k l : Fin n,
      A 0 0 k * A 1 1 l + A 0 0 l * A 1 1 k = A 0 1 k * A 1 0 l + A 0 1 l * A 1 0 k) :
    (∃ p q : F, ¬(p = 0 ∧ q = 0) ∧ ∀ j k, p * A 0 j k + q * A 1 j k = 0) ∨
      (∃ p q : F, ¬(p = 0 ∧ q = 0) ∧ ∀ i k, p * A i 0 k + q * A i 1 k = 0) := by sorry

end DiazModulus
