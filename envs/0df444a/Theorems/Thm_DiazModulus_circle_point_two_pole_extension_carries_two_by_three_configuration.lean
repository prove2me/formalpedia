-- Prove2me | Theorems.Thm_DiazModulus_circle_point_two_pole_extension_carries_two_by_three_configuration
-- name    : DiazModulus.circle_point_two_pole_extension_carries_two_by_three_configuration
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-09T09:01:16.437078+00:00
-- url     : https://prove2.me/theorems/9cdff91f-d194-421e-bd97-a3a72faf9979
-- title:
--   For u ∉ Q̄ with uū algebraic and distinct non-zero algebraic a₁, a₂, the space Q̄ + Q̄u + Q̄ū + Q̄u/(u² − a₁) + Q̄u/(u² − a₂) carries a 2×3 configuration
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ with $\rho = u\bar u$ algebraic, let $a_1 \neq a_2$ be non-zero algebraic numbers, $z_i = u/(u^2 - a_i)$, $H_0 = \overline{\mathbb{Q}} + \overline{\mathbb{Q}}u + \overline{\mathbb{Q}}\bar u$ and $W = H_0 + \overline{\mathbb{Q}}z_1 + \overline{\mathbb{Q}}z_2$. Then there are $x_1, x_2$, linearly independent over $\overline{\mathbb{Q}}$, and $y_1, y_2, y_3$, linearly independent over $\overline{\mathbb{Q}}$, with all six products $x_iy_j$ in $W$.
--
--   The configuration is $x = (1, u^2)$, $y = (b, bu^2, bu^4)$, $b = 1/(u(u^2 - a_1)(u^2 - a_2))$: $W$ contains the progression $b, bu^2, bu^4, bu^6$. For $a_2 = \rho^2/\bar a_1$ this is the first family of `DiazModulus.circle_point_conjugate_pair_extension_carries_two_by_three_configuration`; no conjugation condition is needed here.
--
--   **Proof.** Take $x = (1, u^2)$ and $y = (b, bu^2, bu^4)$ with $b = 1/(u(u^2 - a_1)(u^2 - a_2))$. The six products are $b, bu^2, bu^4, bu^6$, each in $W$ by partial fractions, using $u^{-1} = \bar u/\rho$: $b = (a_1a_2)^{-1}u^{-1} + (a_1(a_1 - a_2))^{-1}z_1 + (a_2(a_2 - a_1))^{-1}z_2$, $bu^2 = (z_1 - z_2)/(a_1 - a_2)$, $bu^4 = (a_1z_1 - a_2z_2)/(a_1 - a_2)$, $bu^6 = u + (a_1^2z_1 - a_2^2z_2)/(a_1 - a_2)$. Both families are free because $u$ is transcendental over $\overline{\mathbb{Q}}$.
--
--   **Novelty.** Not asserted for the shape: it is the progression of Fischler (2001, Lemma 6.1) and Diaz (2007, Th. 7(2)), with ratio $u^2$.
-- source:
--   The configuration is the progression of S. Fischler, Orbits under algebraic groups and logarithms of algebraic numbers, Acta Arith. 100 (2001), 167–187, Lemma 6.1 (p. 184), repeated in G. Diaz, Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques : conjectures et résultats partiels, J. Théor. Nombres Bordeaux 19 (2007), 373–391, Th. 7(2) (p. 390), with ratio u². R7 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 9 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem circle_point_two_pole_extension_carries_two_by_three_configuration (u a₁ a₂ : ℂ)
    (hu : u ∉ Qbar) (hρ : IsAlgebraic ℚ (u * conj u)) (ha₁ : a₁ ∈ Qbar) (ha₂ : a₂ ∈ Qbar)
    (ha₁0 : a₁ ≠ 0) (ha₂0 : a₂ ≠ 0) (ha : a₁ ≠ a₂) :
    ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
      ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, u / (u ^ 2 - a₁), u / (u ^ 2 - a₂)} : Set ℂ) := by
  sorry

end DiazModulus
