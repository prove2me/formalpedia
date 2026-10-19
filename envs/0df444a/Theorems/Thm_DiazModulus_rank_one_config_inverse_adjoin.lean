-- Prove2me | Theorems.Thm_DiazModulus_rank_one_config_inverse_adjoin
-- name    : DiazModulus.rank_one_config_inverse_adjoin
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-16T13:59:07.527893+00:00
-- url     : https://prove2.me/theorems/2b48a58c-dbe5-48ba-92e4-af1c01de5be3
-- title:
--   Over K ≤ F, a 2×3 configuration in V₀ + Ku + Ku⁻¹, with V₀ ⊆ F and u transcendental over F, has its products in V₀
-- statement:
--   Let $K \subseteq F$ be subfields of $\mathbb{C}$, $V_0$ a $K$-subspace of $\mathbb{C}$ contained in $F$, and $u$ transcendental over $F$. If free $x_1, x_2$ and free $y_1, y_2, y_3$ over $K$ have all six products in $V_0 + Ku + Ku^{-1}$, then all six products lie in $V_0$.
--
--   **Proof.** Write $x_iy_j = c_{ij} + l_{ij}u + m_{ij}u^{-1}$ with $c_{ij} \in V_0$ and $l_{ij}, m_{ij} \in K$, and $P_{ij} = l_{ij}X^2 + c_{ij}X + m_{ij} \in F[X]$, so $P_{ij}(u) = ux_iy_j$. The $2 \times 2$ minors of $P$ vanish at $u$, hence vanish, and `DiazModulus.rank_one_polynomial_matrix_factor` gives $P_{ij} = a_ib_j$; the $a_i(u)$ are $K$-free, and so are the $b_j(u)$, being non-zero multiples of $x$ and $y$. If some $m_{ij} \neq 0$: when every $a_i$ is constant, the two $a_i(u)$ lie on one $K$-line; otherwise every $b_j$ has degree at most $1$ and, using that the constant and $X^2$ coefficients of $a_ib_j$ lie in $K$, the three $b_j(u)$ lie in a $K$-span of two numbers. Both are impossible, so every $m_{ij} = 0$; replacing $u$ by $u^{-1}$, which is also transcendental over $F$, gives every $l_{ij} = 0$. So $x_iy_j = c_{ij} \in V_0$.
--
--   **Novelty.** Not found in the sources read in this form. Waldschmidt (*Diophantine Approximation on Linear Algebraic Groups*, Prop. 12.2 and the Remark on p. 424) covers $V_0 = \overline{\mathbb{Q}}$ without $u^{-1}$; the factorisation and degree argument is that of `DiazModulus.generic_circle_point_no_two_by_three_configuration`. Routine.
-- source:
--   Not found in the sources read in this form; it extends M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Springer, 2000, Prop. 12.2 and the Remark on p. 424. Uses DiazModulus.rank_one_polynomial_matrix_factor. R16 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 16 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem rank_one_config_inverse_adjoin (K F : Subfield ℂ) (hKF : K ≤ F)
    (V₀ : Submodule K ℂ) (hV₀ : ∀ v ∈ V₀, v ∈ F) (u : ℂ) (hu : Transcendental F u)
    (x : Fin 2 → ℂ) (y : Fin 3 → ℂ) (hx : LinearIndependent K x) (hy : LinearIndependent K y)
    (hxy : ∀ i j, x i * y j ∈ V₀ ⊔ Submodule.span K ({u, u⁻¹} : Set ℂ)) :
    ∀ i j, x i * y j ∈ V₀ := by
  sorry

end DiazModulus
