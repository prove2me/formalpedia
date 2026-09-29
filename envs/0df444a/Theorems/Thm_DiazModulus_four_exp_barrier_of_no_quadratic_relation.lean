-- Prove2me | Theorems.Thm_DiazModulus_four_exp_barrier_of_no_quadratic_relation
-- name    : DiazModulus.four_exp_barrier_of_no_quadratic_relation
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:34:48.008243+00:00
-- url     : https://prove2.me/theorems/ff0f40a7-c2f2-44ce-803f-5f76aefbeae5
-- title:
--   If numbers satisfy no rational quadratic relation, a singular 2×2 matrix of rational linear forms in them has dependent rows or columns
-- statement:
--   Let $e_1, \dots, e_n \in \mathbb{C}$ satisfy no non-trivial rational quadratic relation: whenever $\sum_{k,l} F_{kl}\, e_k e_l = 0$ with $F_{kl} \in \mathbb{Q}$, the matrix $F$ is alternating, $F_{kl} + F_{lk} = 0$. Let $M$ be a $2 \times 2$ matrix whose entries are rational linear forms in the $e_k$,
--
--   $$M_{ij} = \sum_{k} A_{ijk}\, e_k, \qquad A_{ijk} \in \mathbb{Q}.$$
--
--   If $\det M = 0$, then the rows of $M$, or its columns, are linearly dependent over $\mathbb{Q}$.
--
--   The four exponentials conjecture needs a singular $2 \times 2$ matrix with rows and columns independent over $\mathbb{Q}$. This node says that such a matrix never has entries of this kind. It is the linear-algebra step shared by the `*_four_exp_barrier` nodes.
-- source:
--   Formal proof: Diaz modulus mission, 25 September 2026 (C. Perassi); the step that the four exponentials barrier nodes, such as DiazModulus.generic_conj_pair_four_exp_barrier, carried inline.

import Mathlib

namespace DiazModulus

theorem four_exp_barrier_of_no_quadratic_relation {n : ℕ} (e : Fin n → ℂ)
    (hnq : ∀ F : Fin n → Fin n → ℚ, ∑ k, ∑ l, (F k l : ℂ) * (e k * e l) = 0 →
      ∀ k l, F k l + F l k = 0)
    (A : Fin 2 → Fin 2 → Fin n → ℚ) (M : Fin 2 → Fin 2 → ℂ)
    (hM : ∀ i j, M i j = ∑ k, (A i j k : ℂ) * e k)
    (hdet : M 0 0 * M 1 1 = M 0 1 * M 1 0) :
    (∃ p q : ℚ, ¬(p = 0 ∧ q = 0) ∧ ∀ j, (p : ℂ) * M 0 j + (q : ℂ) * M 1 j = 0) ∨
      (∃ p q : ℚ, ¬(p = 0 ∧ q = 0) ∧ ∀ i, (p : ℂ) * M i 0 + (q : ℂ) * M i 1 = 0) := by
  sorry

end DiazModulus
