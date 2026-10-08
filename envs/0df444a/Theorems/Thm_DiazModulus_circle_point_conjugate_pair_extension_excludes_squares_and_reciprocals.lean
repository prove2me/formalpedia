-- Prove2me | Theorems.Thm_DiazModulus_circle_point_conjugate_pair_extension_excludes_squares_and_reciprocals
-- name    : DiazModulus.circle_point_conjugate_pair_extension_excludes_squares_and_reciprocals
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-06T07:48:11.724874+00:00
-- url     : https://prove2.me/theorems/f640cf63-2fec-48d4-b85e-1eff3f39da34
-- title:
--   For the same u, a and z, the space Q̄ + Q̄u + Q̄ū + Q̄z + Q̄z̄ contains none of u², ū² and 1/(u − b) with b ∈ Q̄ non-zero
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ with $\rho = u\bar u$ algebraic, let $a \in \overline{\mathbb{Q}}$, $a \neq 0$, and let $z$ be $u/(u^2 - a)$ if $a\bar a \neq \rho^2$, or $u/(u^2 - a)^2$ if $a\bar a = \rho^2$. Put $H_0 = \overline{\mathbb{Q}} + \overline{\mathbb{Q}}u + \overline{\mathbb{Q}}\bar u$ and $W = H_0 + \overline{\mathbb{Q}}z + \overline{\mathbb{Q}}\bar z$. Then $W$ contains neither $u^2$ nor $\bar u^2$, nor $1/(u - b)$ for any $b \in \overline{\mathbb{Q}}$, $b \neq 0$.
--
--   These are the elements $w$ for which, by Theorem B (`DiazModulus.circle_point_extension_two_by_three_configuration_iff`), a four-dimensional space $H_0 + \overline{\mathbb{Q}}w$ carries a configuration; so no such space lies inside $W$.
--
--   **Proof.** Both cases have the shape $z\,Q_1(u^2) = u\,R_1(u^2)$ and $\bar z\,Q_2(u^2) = u\,R_2(u^2)$ with $Q_1(0), Q_2(0) \neq 0$: in the first, $Q_1 = X - a$, $R_1 = 1$, $Q_2 = X - a'$, $R_2 = \kappa$ with $a' = \rho^2/\bar a$ and $\kappa = -\rho/\bar a$; in the second, $Q_1 = Q_2 = (X - a)^2$, $R_1 = 1$, $R_2 = \kappa X$ with $\kappa = \rho/\bar a^2$. Every element of $W$ is $c_1 + c_2u + c_3\bar u + c_4z + c_5\bar z$ with $c_i \in \overline{\mathbb{Q}}$, and $\bar u = \rho u^{-1}$. Clearing denominators turns a membership into $A(u^2) + u\,B(u^2) = 0$ with $A, B \in \overline{\mathbb{Q}}[X]$. This forces $A = B = 0$: the same polynomial identity holds at $-u$, so adding gives $A(u^2) = 0$, and $u^2$ is transcendental. For $u^2$ the odd part is $B = (X - c_1)Q_1Q_2 \neq 0$. For $\bar u^2 = \rho^2u^{-2}$ the even part is $A = (\rho^2 - c_1X)Q_1Q_2$, and $A(0) = \rho^2Q_1(0)Q_2(0) \neq 0$. For $1/(u - b) = (u + b)/(u^2 - b^2)$ the odd part is $B = Q_1Q_2\,(b - c_1(X - b^2))$, whose last factor takes the value $b \neq 0$ at $X = b^2$. The hypothesis $a\bar a \neq \rho^2$ of the first case is not used.
--
--   **Novelty.** Not asserted separately; elementary (parity in $u$).
-- source:
--   Elementary (parity in u and the transcendence of u). A step of R5 of the Diaz modulus mission (DiazModulus.circle_point_conjugate_pair_configuration_invisible_to_four_dimensional_extensions). Formal proof: Diaz modulus mission, 6 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem circle_point_conjugate_pair_extension_excludes_squares_and_reciprocals (u a z : ℂ)
    (hu : u ∉ Qbar) (hρ : IsAlgebraic ℚ (u * conj u)) (ha : a ∈ Qbar) (ha0 : a ≠ 0)
    (hz : (a * conj a ≠ (u * conj u) ^ 2 ∧ z = u / (u ^ 2 - a)) ∨
      (a * conj a = (u * conj u) ^ 2 ∧ z = u / (u ^ 2 - a) ^ 2)) :
    u ^ 2 ∉ Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ) ∧
      conj u ^ 2 ∉ Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ) ∧
      ∀ b ∈ Qbar, b ≠ 0 → (u - b)⁻¹ ∉ Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ) := by
  sorry

end DiazModulus
