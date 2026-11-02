-- Prove2me | Theorems.Thm_DiazModulus_invisible_cyclic_space_configuration_ratio_mobius
-- name    : DiazModulus.invisible_cyclic_space_configuration_ratio_mobius
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-01T09:19:59.07619+00:00
-- url     : https://prove2.me/theorems/fbcee3fe-38c2-4fd0-b472-89dba34c9192
-- title:
--   Q1.6, cyclic: every configuration in an invisible cyclic space has ratio a Möbius function of P(u)/Q(u); the involution is unique, ramified orbits included
-- statement:
--   Let $u \in \mathbb{C}$ be transcendental, that is, $u \notin \overline{\mathbb{Q}}$ (the algebraic numbers); spans and linear independence are over $\overline{\mathbb{Q}}$. Let $P, Q, S_1, S_2 \in \overline{\mathbb{Q}}[X]$ with $P, Q$ coprime, $\max(\deg P, \deg Q) = 2$ and $\deg S_1, \deg S_2 \leq 2$. Put $g_1 = Q(u)S_1(u)/(uP(u))$, $g_2 = Q(u)(Q(u)S_1(u) + P(u)S_2(u))/(uP(u)^2)$ and $W_B = \mathrm{span}(1, u, u^{-1}, g_1, g_2)$, the cyclic shape (D2b) of Theorem NF. Suppose that $P$ and $S_1$ have no common zero on the projective line: they are coprime, and their coefficients of $X^2$ are not both zero. Let $x_0, x_1 \in \mathbb{C}$ be linearly independent and $y_0, y_1, y_2 \in \mathbb{C}$ linearly independent, with $x_iy_j \in W_B$ for all $i, j$ (a $2 \times 3$ configuration in $W_B$). Then there are $a, b, c, d \in \overline{\mathbb{Q}}$ with $ad - bc \neq 0$ and $x_1(cP(u) + dQ(u)) = x_0(aP(u) + bQ(u))$, that is, $x_1/x_0$ is a Möbius function of $P(u)/Q(u)$.
--
--   $W_B$ carries the configuration with $x = (1, P(u)/Q(u))$ (`DiazModulus.quadratic_cyclic_space_carries_two_by_three_configuration`). So every configuration of an invisible cyclic space has its ratio in $\overline{\mathbb{Q}}(P(u)/Q(u))$, and the involution of the research notes is unique, also when the orbit is a double zero of $P$ (a ramified orbit), passes through $0$ or $\infty$, or $P$ is constant. Two polynomials $P, S \in \overline{\mathbb{Q}}[X]$ of degree at most $2$ have a common zero on the projective line if they are not coprime (a common root in $\overline{\mathbb{Q}}$) or their coefficients of $X^2$ are both zero (a common zero at $\infty$, reading $P$ and $S$ as binary forms of degree $2$).
--
--   **Proof.** As in the two-orbit case, with `DiazModulus.invisible_cyclic_space_u_multiplier_space_eq`, `DiazModulus.u_multiplier_space_le_span_no_degree_one_no_visible_element`, `DiazModulus.configuration_ratio_quadratic_of_not_degree_one` and `DiazModulus.degree_two_configuration_pencil_normal_form`: $x_1/x_0 = p(u)/q(u)$, and an invertible combination $(P', Q')$ of $(p, q)$ gives three cases. Scalar: excluded by `DiazModulus.scalar_quadratic_space_visible_element_mem`. Two-orbit: `DiazModulus.invisible_cyclic_space_pole_pencil`, applied to the generators $Q'(u)S_1'(u)/(uP'(u))$ and $P'(u)S_2'(u)/(uQ'(u))$, makes both $P'$ and $Q'$ multiples of $P$, against coprimality. Cyclic: `DiazModulus.invisible_cyclic_space_pole_pencil` gives $P' = \kappa P$ and $Q'(u)S_1'(u)/(uP'(u)) = R_0(u)/u + \mu' g_1$ with $\mu' \neq 0$; `DiazModulus.quadratic_space_mem_iff_numerator` writes the second generator of $W_B$ over $uP(u)^2$, with coefficient $\mu$ on $g_2$. Eliminating gives $QS_1(\mu'Q' - \kappa\mu Q) = P \cdot B$ with $\deg B \leq 4$, and `DiazModulus.binary_quadratic_dvd_of_coprime_mul_eq` ($d = 4$, $e = 2$) gives $\mu'Q' = \kappa\mu Q + c_0P$ for some $c_0 \in \overline{\mathbb{Q}}$; $\mu \neq 0$ because $P'$, $Q'$ are coprime. So $(P', Q')$ is an invertible combination of $(P, Q)$, and so is $(p, q)$.
--
--   **Novelty.** None claimed; routine. It is Q1.6 of the project's research notes (R12) for cyclic spaces. The cyclic core is the identity $QS_1(\mu'Q' - \kappa\mu Q) = P \cdot B$ with $\deg B \leq 4$, to which `DiazModulus.binary_quadratic_dvd_of_coprime_mul_eq` applies with $d = 4$, $e = 2$; the same lines cover an orbit through $0$ or $\infty$ and a double zero of $P$.
-- source:
--   No novelty claimed. Q1.6 of the Diaz modulus mission's research notes (round R12), for cyclic spaces at every orbit position, proved here by divisibility of binary forms. Uses DiazModulus.invisible_cyclic_space_u_multiplier_space_eq, DiazModulus.u_multiplier_space_le_span_no_degree_one_no_visible_element, DiazModulus.scalar_quadratic_space_visible_element_mem, DiazModulus.degree_two_configuration_pencil_normal_form, DiazModulus.configuration_ratio_quadratic_of_not_degree_one, DiazModulus.invisible_cyclic_space_pole_pencil, DiazModulus.quadratic_space_mem_iff_numerator, DiazModulus.binary_quadratic_dvd_of_coprime_mul_eq and DiazModulus.coprime_pencil_mobius. R21b of the Diaz modulus mission. Formal proof: Diaz modulus mission, 30 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Polynomial in
theorem invisible_cyclic_space_configuration_ratio_mobius (u : ℂ) (hu : u ∉ Qbar) (P Q S₁ S₂ : (↥Qbar)[X])
    (hcop : IsCoprime P Q) (hdeg : max P.natDegree Q.natDegree = 2) (hS₁ : S₁.natDegree ≤ 2) (hS₂ : S₂.natDegree ≤ 2)
    (hPS : IsCoprime P S₁) (hP2 : P.coeff 2 ≠ 0 ∨ S₁.coeff 2 ≠ 0)
    (x : Fin 2 → ℂ) (y : Fin 3 → ℂ) (hx : LinearIndependent (↥Qbar) x) (hy : LinearIndependent (↥Qbar) y)
    (hxy : ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P),
        aeval u Q * (aeval u Q * aeval u S₁ + aeval u P * aeval u S₂) / (u * aeval u P ^ 2)} : Set ℂ)) :
    ∃ a b c d : ℂ, a ∈ Qbar ∧ b ∈ Qbar ∧ c ∈ Qbar ∧ d ∈ Qbar ∧ a * d - b * c ≠ 0 ∧
      x 1 * (c * aeval u P + d * aeval u Q) = x 0 * (a * aeval u P + b * aeval u Q) := by
  sorry

end DiazModulus
