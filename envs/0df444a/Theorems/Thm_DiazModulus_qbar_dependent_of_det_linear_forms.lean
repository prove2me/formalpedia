-- Prove2me | Theorems.Thm_DiazModulus_qbar_dependent_of_det_linear_forms
-- name    : DiazModulus.qbar_dependent_of_det_linear_forms
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:16:00.430859+00:00
-- url     : https://prove2.me/theorems/68d6a676-e5c6-4cf0-ac07-342afc64d259
-- title:
--   A 2×2 block of products whose determinant vanishes as a form has an algebraic row or column relation
-- statement:
--   Let $e_1, \dots, e_4 \in \mathbb{C}$, and let $x_0, x_1, y_{j_0}, y_{j_1} \in \mathbb{C}$ with $x_0 \neq 0$ and $y_{j_0} \neq 0$. Suppose that each product is an algebraic linear form in the $e_k$,
--
--   $$x_i\, y_j = L_{ij}(e) = \sum_{k} c_{ijk}\, e_k, \qquad c_{ijk} \in \overline{\mathbb{Q}},$$
--
--   and that the determinant of the block vanishes identically as a quadratic form:
--
--   $$L_{0 j_0}(z)\, L_{1 j_1}(z) - L_{0 j_1}(z)\, L_{1 j_0}(z) = 0 \quad \text{for all } z \in \mathbb{C}^{4}.$$
--
--   Then $x_0, x_1$ or $y_{j_0}, y_{j_1}$ are linearly dependent over $\overline{\mathbb{Q}}$.
--
--   The numerical determinant $x_0 y_{j_0} \cdot x_1 y_{j_1} - x_0 y_{j_1} \cdot x_1 y_{j_0}$ is always zero; the hypothesis is the identity of forms. It arises when a quadratic relation among the $e_k$ is known to be a multiple of a fixed form, as in `DiazModulus.generic_no_strong_six_exp_configuration`.
-- source:
--   Standard linear algebra. Formal proof: Diaz modulus mission, 25 September 2026 (C. Perassi); extracted from the proofs of DiazModulus.generic_no_strong_six_exp_configuration and DiazModulus.generic_qbar_homogeneous_four_exp_barrier.

import Definitions.Def_DiazModulus

namespace DiazModulus

theorem qbar_dependent_of_det_linear_forms {m : ℕ} (e : Fin 4 → ℂ) (C : Fin 2 → Fin m → Fin 4 → ℂ)
    (hC : ∀ i j k, IsAlgebraic ℚ (C i j k)) (x : Fin 2 → ℂ) (y : Fin m → ℂ) (j0 j1 : Fin m)
    (hx0 : x 0 ≠ 0) (hy0 : y j0 ≠ 0)
    (hxy : ∀ i j, x i * y j = ∑ k, C i j k * e k)
    (hdet : ∀ z : Fin 4 → ℂ, (∑ k, C 0 j0 k * z k) * (∑ k, C 1 j1 k * z k)
      - (∑ k, C 0 j1 k * z k) * (∑ k, C 1 j0 k * z k) = 0) :
    (∃ p q : ↥Qbar, ¬(p = 0 ∧ q = 0) ∧ (p : ℂ) * x 0 + (q : ℂ) * x 1 = 0) ∨
      (∃ p q : ↥Qbar, ¬(p = 0 ∧ q = 0) ∧ (p : ℂ) * y j0 + (q : ℂ) * y j1 = 0) := by
  sorry

end DiazModulus
