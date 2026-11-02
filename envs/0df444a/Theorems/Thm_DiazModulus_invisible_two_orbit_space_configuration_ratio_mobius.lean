-- Prove2me | Theorems.Thm_DiazModulus_invisible_two_orbit_space_configuration_ratio_mobius
-- name    : DiazModulus.invisible_two_orbit_space_configuration_ratio_mobius
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-01T09:20:09.830165+00:00
-- url     : https://prove2.me/theorems/1c0d8b3a-c510-4269-b568-f601a4547f0d
-- title:
--   Q1.6, two-orbit: every configuration in an invisible two-orbit space has ratio a Möbius function of P(u)/Q(u); the involution is unique
-- statement:
--   Let $u \in \mathbb{C}$ be transcendental, that is, $u \notin \overline{\mathbb{Q}}$ (the algebraic numbers); spans and linear independence are over $\overline{\mathbb{Q}}$. Let $P, Q, S_1, S_2 \in \overline{\mathbb{Q}}[X]$ with $P, Q$ coprime, $\max(\deg P, \deg Q) = 2$ and $\deg S_1, \deg S_2 \leq 2$. Put $g_1 = Q(u)S_1(u)/(uP(u))$, $g_2 = P(u)S_2(u)/(uQ(u))$ and $W_A = \mathrm{span}(1, u, u^{-1}, g_1, g_2)$, the two-orbit shape (D2a) of Theorem NF. Suppose that $P$ and $S_1$ have no common zero on the projective line, and neither have $Q$ and $S_2$: $P, S_1$ are coprime, $Q, S_2$ are coprime, the coefficients of $X^2$ in $P$ and $S_1$ are not both zero, and those in $Q$ and $S_2$ are not both zero. Let $x_0, x_1 \in \mathbb{C}$ be linearly independent and $y_0, y_1, y_2 \in \mathbb{C}$ linearly independent, with $x_iy_j \in W_A$ for all $i, j$ (a $2 \times 3$ configuration in $W_A$). Then there are $a, b, c, d \in \overline{\mathbb{Q}}$ with $ad - bc \neq 0$ and $x_1(cP(u) + dQ(u)) = x_0(aP(u) + bQ(u))$, that is, $x_1/x_0$ is a Möbius function of $P(u)/Q(u)$.
--
--   $W_A$ carries the configuration with $x = (1, P(u)/Q(u))$ (`DiazModulus.quadratic_two_orbit_space_carries_two_by_three_configuration`). So every configuration of an invisible two-orbit space has its ratio in $\overline{\mathbb{Q}}(P(u)/Q(u))$, and the involution of the research notes, which exchanges the points of each fibre of $P/Q$, is unique. Two polynomials $P, S \in \overline{\mathbb{Q}}[X]$ of degree at most $2$ have a common zero on the projective line if they are not coprime (a common root in $\overline{\mathbb{Q}}$) or their coefficients of $X^2$ are both zero (a common zero at $\infty$, reading $P$ and $S$ as binary forms of degree $2$). The hypothesis on common zeros is needed: $\mathrm{span}(u^{-2}, u^{-1}, 1, u, u^2)$, which is $W_A$ for $P = X^2 - X$, $Q = 1$, $S_1 = X - 1$, $S_2 = X$ (here $P$ and $S_1$ share the root $1$), carries configurations with ratios $u^2 - u$ and $u^2$, and neither is a Möbius function of the other.
--
--   **Proof.** By `DiazModulus.invisible_two_orbit_space_u_multiplier_space_eq`, $\dim W_A = 5$ and (D1) fails; by `DiazModulus.u_multiplier_space_le_span_no_degree_one_no_visible_element`, $W_A$ contains none of $u^2$, $u^{-2}$, $(u - a)^{-1}$. As $W_A \subseteq \overline{\mathbb{Q}}(u)$, `DiazModulus.configuration_ratio_quadratic_of_not_degree_one` writes $x_1/x_0 = p(u)/q(u)$ with $p, q$ coprime of maximal degree $2$, and `DiazModulus.degree_two_configuration_pencil_normal_form` gives an invertible combination $(P', Q')$ of $(p, q)$ with three cases. Scalar: `DiazModulus.scalar_quadratic_space_visible_element_mem` would put one of the excluded elements in $W_A$. Two-orbit, $W_A = \mathrm{span}(1, u, u^{-1}, Q'(u)S_1'(u)/(uP'(u)), P'(u)S_2'(u)/(uQ'(u)))$: the last two generators lie outside $H_0$ (dimension $5$), so `DiazModulus.invisible_two_orbit_space_pole_pencil` makes each of $P'$, $Q'$ proportional to $P$ or to $Q$, and not both to the same one. Cyclic: `DiazModulus.invisible_two_orbit_space_pole_pencil` makes $P' = \kappa P$ or $\kappa Q$; then $P(u)S_2(u)/(uQ(u))$ (resp. $g_1$) lies in the cyclic span of $(P', Q')$, and `DiazModulus.quadratic_space_mem_iff_numerator` gives $\kappa^2P^3S_2 = QN$ with $\deg N \leq 6$ (resp. the symmetric identity), which `DiazModulus.binary_quadratic_dvd_of_coprime_mul_eq` ($e = 0$, $d = 8$) excludes. So $(P', Q')$ is an invertible combination of $(P, Q)$, and so is $(p, q)$.
--
--   **Novelty.** None claimed; routine. It is Q1.6 of the project's research notes (R12) for two-orbit spaces. The proof compares two normal forms of the same space through `DiazModulus.invisible_two_orbit_space_pole_pencil` and the division lemma `DiazModulus.binary_quadratic_dvd_of_coprime_mul_eq`.
-- source:
--   No novelty claimed. Q1.6 of the Diaz modulus mission's research notes (round R12), for two-orbit spaces, proved here by divisibility of binary forms. Uses DiazModulus.invisible_two_orbit_space_u_multiplier_space_eq, DiazModulus.u_multiplier_space_le_span_no_degree_one_no_visible_element, DiazModulus.scalar_quadratic_space_visible_element_mem, DiazModulus.degree_two_configuration_pencil_normal_form, DiazModulus.configuration_ratio_quadratic_of_not_degree_one, DiazModulus.invisible_two_orbit_space_pole_pencil, DiazModulus.quadratic_space_mem_iff_numerator, DiazModulus.binary_quadratic_dvd_of_coprime_mul_eq and DiazModulus.coprime_pencil_mobius. R21b of the Diaz modulus mission. Formal proof: Diaz modulus mission, 30 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Polynomial in
theorem invisible_two_orbit_space_configuration_ratio_mobius (u : ℂ) (hu : u ∉ Qbar) (P Q S₁ S₂ : (↥Qbar)[X])
    (hcop : IsCoprime P Q) (hdeg : max P.natDegree Q.natDegree = 2) (hS₁ : S₁.natDegree ≤ 2) (hS₂ : S₂.natDegree ≤ 2)
    (hPS : IsCoprime P S₁) (hQS : IsCoprime Q S₂)
    (hP2 : P.coeff 2 ≠ 0 ∨ S₁.coeff 2 ≠ 0) (hQ2 : Q.coeff 2 ≠ 0 ∨ S₂.coeff 2 ≠ 0)
    (x : Fin 2 → ℂ) (y : Fin 3 → ℂ) (hx : LinearIndependent (↥Qbar) x) (hy : LinearIndependent (↥Qbar) y)
    (hxy : ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P),
        aeval u P * aeval u S₂ / (u * aeval u Q)} : Set ℂ)) :
    ∃ a b c d : ℂ, a ∈ Qbar ∧ b ∈ Qbar ∧ c ∈ Qbar ∧ d ∈ Qbar ∧ a * d - b * c ≠ 0 ∧
      x 1 * (c * aeval u P + d * aeval u Q) = x 0 * (a * aeval u P + b * aeval u Q) := by
  sorry

end DiazModulus
