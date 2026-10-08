-- Prove2me | Theorems.Thm_DiazModulus_circle_point_config_constant_matrix_det_ne_zero
-- name    : DiazModulus.circle_point_config_constant_matrix_det_ne_zero
-- status  : Open
-- author  : @carlok
-- created : 2026-10-08T13:10:53.554559+00:00
-- url     : https://prove2.me/theorems/51102291-6ce5-46ee-babb-35310b185431
-- title:
--   For u, w₁…w_m algebraically independent over a subfield K of ℂ with uū ∈ K, every 2×2 configuration over K in K + Ku + Kū + ΣKw_k has an invertible matrix of constant terms
-- statement:
--   A $p \times q$ configuration over a field $K$ in a $K$-subspace $V \subseteq \mathbb{C}$ is a pair $x_1, \dots, x_p$ and $y_1, \dots, y_q$ of complex numbers, each family linearly independent over $K$, with every product $x_iy_j$ in $V$; it is the input of Roy's strong six exponentials theorem when $p = 2$, $q = 3$, $K = \overline{\mathbb{Q}}$ and $V = \widetilde{\mathcal{L}}$.
--
--   Let $K$ be a subfield of $\mathbb{C}$, let $u, w_1, \dots, w_m$ be algebraically independent over $K$, suppose $\rho = u\bar u \in K$, and put $H_0 = K + Ku + K\bar u$. For every $2 \times 2$ configuration $x, y$ over $K$ in $H_0 + Kw_1 + \dots + Kw_m$ there is an invertible $c \in K^{2 \times 2}$ with $x_iy_j - c_{ij} \in Ku + K\bar u$ for all $i, j$.
--
--   So every row and every column of $(x_iy_j)$ has an entry with non-zero constant term, and no $2 \times 2$ configuration lies in $Ku + K\bar u + Kw_1 + \dots + Kw_m$. The constant matrix is $P\,\mathrm{diag}(1, \rho)\,Q$ in the normal form `DiazModulus.circle_point_two_by_two_normal_form`.
--
--   **Proof.** By `DiazModulus.generic_circle_point_config_is_two_by_two` the products lie in $H_0$, and the normal form (`DiazModulus.circle_point_two_by_two_normal_form`) gives $x_i = \mu(P_{i1} + P_{i2}u)$, $y_j = \mu^{-1}(Q_{1j} + Q_{2j}\bar u)$. Expanding with $u\bar u = \rho$: $x_iy_j = c_{ij} + P_{i2}Q_{1j}u + P_{i1}Q_{2j}\bar u$ with $c = P\,\mathrm{diag}(1, \rho)\,Q$, and $\det c = \rho\det P\det Q \neq 0$.
--
--   **Novelty.** Not found in the sources read; it is short. It sharpens `DiazModulus.generic_qbar_homogeneous_four_exp_barrier` (no configuration in $\overline{\mathbb{Q}}u + \overline{\mathbb{Q}}\bar u + \overline{\mathbb{Q}}i\pi$) to any base field and any number of generic numbers, and says the constant matrix is invertible, not only non-zero.
-- source:
--   Not found in the sources read; sharpens DiazModulus.generic_qbar_homogeneous_four_exp_barrier. R6 of the Diaz modulus mission (the polar-degree note). Formal proof: Diaz modulus mission, 8 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem circle_point_config_constant_matrix_det_ne_zero (K : Subfield ℂ) (u : ℂ)
    (hρ : u * conj u ∈ K) (m : ℕ) (w : Fin m → ℂ)
    (hgen : AlgebraicIndependent K (Fin.cons u w : Fin (m + 1) → ℂ))
    (x y : Fin 2 → ℂ) (hx : LinearIndependent K x) (hy : LinearIndependent K y)
    (hxy : ∀ i j, x i * y j ∈ Submodule.span K (({1, u, conj u} : Set ℂ) ∪ Set.range w)) :
    ∃ c : Matrix (Fin 2) (Fin 2) K, c.det ≠ 0 ∧
      ∀ i j, x i * y j - (c i j : ℂ) ∈ Submodule.span K ({u, conj u} : Set ℂ) := by
  sorry

end DiazModulus
