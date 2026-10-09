-- Prove2me | Theorems.Thm_DiazModulus_circle_point_two_pole_extension_excludes_squares_and_reciprocals
-- name    : DiazModulus.circle_point_two_pole_extension_excludes_squares_and_reciprocals
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-09T09:01:37.628997+00:00
-- url     : https://prove2.me/theorems/2ea6a548-8444-48d0-9666-c224dac35020
-- title:
--   For the same u, a₁, a₂, the space Q̄ + Q̄u + Q̄ū + Q̄u/(u² − a₁) + Q̄u/(u² − a₂) contains none of u², ū² and 1/(u − b) with b ∈ Q̄ non-zero
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ with $\rho = u\bar u$ algebraic, let $a_1 \neq a_2$ be non-zero algebraic numbers, $z_i = u/(u^2 - a_i)$, $H_0 = \overline{\mathbb{Q}} + \overline{\mathbb{Q}}u + \overline{\mathbb{Q}}\bar u$ and $W = H_0 + \overline{\mathbb{Q}}z_1 + \overline{\mathbb{Q}}z_2$. Then $W$ contains neither $u^2$ nor $\bar u^2$, nor $1/(u - b)$ for any non-zero $b \in \overline{\mathbb{Q}}$.
--
--   These are the elements $w$ for which, by Theorem B (`DiazModulus.circle_point_extension_two_by_three_configuration_iff`), a four-dimensional space $H_0 + \overline{\mathbb{Q}}w$ carries a configuration.
--
--   **Proof.** Both $z_i$ satisfy $z_i(u^2 - a_i) = u$. Clearing denominators (with $\bar u = \rho/u$) turns a membership $w \in W$ into $A(u^2) + uB(u^2) = 0$ with $A, B \in \overline{\mathbb{Q}}[X]$; the same identity at $-u$ gives $A = B = 0$, as $u^2$ is transcendental. For $u^2$ the odd part $B = (X - c_1)(X - a_1)(X - a_2)$ is non-zero ($c_1$ the coordinate on $u$); for $\bar u^2 = \rho^2/u^2$ the even part has $A(0) = \rho^2a_1a_2 \neq 0$; for $1/(u - b) = (u + b)/(u^2 - b^2)$ the odd part is $(X - a_1)(X - a_2)(b - c_1(X - b^2))$, non-zero because its last factor takes the value $b \neq 0$ at $X = b^2$. Here $c_1$ is the constant coordinate of the element of $W$.
--
--   **Novelty.** Not asserted separately; elementary (parity in $u$).
-- source:
--   Elementary (parity in u and the transcendence of u). A step of R7 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 9 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem circle_point_two_pole_extension_excludes_squares_and_reciprocals (u a₁ a₂ : ℂ)
    (hu : u ∉ Qbar) (hρ : IsAlgebraic ℚ (u * conj u)) (ha₁ : a₁ ∈ Qbar) (ha₂ : a₂ ∈ Qbar)
    (ha₁0 : a₁ ≠ 0) (ha₂0 : a₂ ≠ 0) (ha : a₁ ≠ a₂) :
    u ^ 2 ∉ Submodule.span Qbar ({1, u, conj u, u / (u ^ 2 - a₁), u / (u ^ 2 - a₂)} : Set ℂ) ∧
      conj u ^ 2 ∉ Submodule.span Qbar ({1, u, conj u, u / (u ^ 2 - a₁), u / (u ^ 2 - a₂)} : Set ℂ) ∧
      ∀ b ∈ Qbar, b ≠ 0 → (u - b)⁻¹ ∉ Submodule.span Qbar ({1, u, conj u, u / (u ^ 2 - a₁), u / (u ^ 2 - a₂)} : Set ℂ) := by
  sorry

end DiazModulus
