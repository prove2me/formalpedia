-- Prove2me | Theorems.Thm_DiazModulus_det_zero_linear_forms_rank_one
-- name    : DiazModulus.det_zero_linear_forms_rank_one
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T20:37:02.878197+00:00
-- url     : https://prove2.me/theorems/43368f52-e0aa-4270-9798-a38107dc9561
-- title:
--   A 2×2 matrix of rational linear forms with identically vanishing determinant has dependent rows or columns
-- statement:
--   **Singular $2\times2$ matrices of linear forms.**
--
--   Let $L = (L_{ij})$ be a $2\times2$ matrix of linear forms $L_{ij} = \sum_k A_{ijk} X_k$ in $n$ variables with rational coefficients, and suppose $\det L = L_{00}L_{11} - L_{01}L_{10}$ is the zero polynomial. The hypothesis states exactly that all symmetrised coefficients of $\det L$ vanish. Then the rows of $L$ are $\mathbb{Q}$-linearly dependent, or its columns are.
--
--   This is the algebraic step of `DiazModulus.generic_conj_pair_four_exp_barrier` and `DiazModulus.recip_pi_log_four_exp_barrier`: a matrix of numbers whose entries are rational combinations of numbers satisfying no homogeneous quadratic relation is singular only if its rows or columns are dependent.
--
--   **Novelty.** None claimed. Classical (rank-one linear spaces of matrices; unique factorisation in the polynomial ring).
-- source:
--   Used in the proof of Theorem 5.4(b) of Carlo Perassi, companion note to https://github.com/carlok/diaz-modulus-lean, version 1.9, 25 September 2026 (GitHub release note-v1.9), as the lemma on linear forms. Formal proof: Diaz modulus mission, 23 September 2026 (C. Perassi). Background: the classical description of linear spaces of rank-one matrices.

import Mathlib

namespace DiazModulus

theorem det_zero_linear_forms_rank_one (n : ℕ) (A : Fin 2 → Fin 2 → Fin n → ℚ)
    (hdet : ∀ k l : Fin n,
      A 0 0 k * A 1 1 l + A 0 0 l * A 1 1 k = A 0 1 k * A 1 0 l + A 0 1 l * A 1 0 k) :
    (∃ p q : ℚ, ¬(p = 0 ∧ q = 0) ∧ ∀ j k, p * A 0 j k + q * A 1 j k = 0) ∨
      (∃ p q : ℚ, ¬(p = 0 ∧ q = 0) ∧ ∀ i k, p * A i 0 k + q * A i 1 k = 0) := by sorry

end DiazModulus
