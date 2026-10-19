-- Prove2me | Theorems.Thm_DiazModulus_config_shifted_coprime_polynomial_factors
-- name    : DiazModulus.config_shifted_coprime_polynomial_factors
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-18T14:27:55.326643+00:00
-- url     : https://prove2.me/theorems/da34735d-85f7-4c2a-96d2-f7984742592c
-- title:
--   A 2×3 configuration whose products times u^N are values at u of polynomials in H factors through coprime a₀, a₁ and free b₀, b₁, b₂ with aᵢbⱼ ∈ H
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$, let $H \subseteq \overline{\mathbb{Q}}[X]$ be a $\overline{\mathbb{Q}}$-subspace and $N \geq 0$. Let $x_0, x_1 \in \mathbb{C}$ be linearly independent over $\overline{\mathbb{Q}}$, and $y_0, y_1, y_2 \in \mathbb{C}$ too, such that for all $i, j$ there is $Q_{ij} \in H$ with $Q_{ij}(u) = u^Nx_iy_j$. Then there are coprime $a_0, a_1 \in \overline{\mathbb{Q}}[X]$ and linearly independent $b_0, b_1, b_2 \in \overline{\mathbb{Q}}[X]$ with $a_ib_j \in H$ for all $i, j$ and $x_1a_0(u) = x_0a_1(u)$.
--
--   **Proof.** As $u$ is transcendental over $\overline{\mathbb{Q}}$, evaluation at $u$ is injective on $\overline{\mathbb{Q}}[X]$. Each $Q_{ij}$ is non-zero, and the $2 \times 2$ minors $Q_{ij}Q_{i'j'} - Q_{ij'}Q_{i'j}$ vanish at $u$, hence vanish; `DiazModulus.rank_one_polynomial_matrix_factor` gives $Q_{ij} = a_ib_j$ with $a_0, a_1$ coprime, so $a_ib_j \in H$. The $b_j(u) = (u^Nx_0/a_0(u))\,y_j$ are a non-zero multiple of the free family $y$, so $b$ is free; and $x_1a_0(u)b_0(u) = u^Nx_0x_1y_0 = x_0a_1(u)b_0(u)$, where $b_0(u) \neq 0$ cancels.
--
--   **Novelty.** Not found in the sources read in this form; routine. It is the normalisation of `DiazModulus.config_shifted_polynomial_spans`, sharpened by the rank-one factorisation `DiazModulus.rank_one_polynomial_matrix_factor`.
-- source:
--   Not found in the sources read in this form; it sharpens the normalisation of DiazModulus.config_shifted_polynomial_spans. Uses DiazModulus.rank_one_polynomial_matrix_factor. R18 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 18 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Polynomial in
theorem config_shifted_coprime_polynomial_factors {u : ℂ} (hu : u ∉ Qbar)
    (Hull : Submodule (↥Qbar) (↥Qbar)[X]) (N : ℕ)
    (x : Fin 2 → ℂ) (y : Fin 3 → ℂ) (hx : LinearIndependent (↥Qbar) x)
    (hy : LinearIndependent (↥Qbar) y)
    (hxy : ∀ i j, ∃ Q ∈ Hull, aeval u Q = u ^ N * (x i * y j)) :
    ∃ (a : Fin 2 → (↥Qbar)[X]) (b : Fin 3 → (↥Qbar)[X]), IsCoprime (a 0) (a 1) ∧
      LinearIndependent (↥Qbar) b ∧ (∀ i j, a i * b j ∈ Hull) ∧
      x 1 * aeval u (a 0) = x 0 * aeval u (a 1) := by
  sorry

end DiazModulus
