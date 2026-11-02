-- Prove2me | Theorems.Thm_DiazModulus_conj_stable_invisible_quadratic_space_conj_ratio_mobius
-- name    : DiazModulus.conj_stable_invisible_quadratic_space_conj_ratio_mobius
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-01T09:19:50.699775+00:00
-- url     : https://prove2.me/theorems/1645cede-dbf4-49e7-ab41-f64ec0b5ece2
-- title:
--   Q1.7: in a conjugation-stable invisible degree-two space, conj(P(u)/Q(u)) is a Möbius function of P(u)/Q(u), that is, σ τ σ = τ
-- statement:
--   Let $u \in \mathbb{C}$ be transcendental, that is, $u \notin \overline{\mathbb{Q}}$ (the algebraic numbers); spans and linear independence are over $\overline{\mathbb{Q}}$. Let $P, Q, S_1, S_2 \in \overline{\mathbb{Q}}[X]$ with $P, Q$ coprime, $\max(\deg P, \deg Q) = 2$ and $\deg S_1, \deg S_2 \leq 2$. Let $W$ be either $W_A = \mathrm{span}(1, u, u^{-1}, g_1, g_2)$ with $g_2 = P(u)S_2(u)/(uQ(u))$, where $P, S_1$ and $Q, S_2$ have no common zero on the projective line, or $W_B = \mathrm{span}(1, u, u^{-1}, g_1, g_2')$ with $g_2' = Q(u)(Q(u)S_1(u) + P(u)S_2(u))/(uP(u)^2)$, where $P, S_1$ have no common zero on the projective line; in both, $g_1 = Q(u)S_1(u)/(uP(u))$. Suppose $W$ is stable under complex conjugation. Then there are $a, b, c, d \in \overline{\mathbb{Q}}$ with $ad - bc \neq 0$ and $\overline{P(u)}\,(cP(u) + dQ(u)) = \overline{Q(u)}\,(aP(u) + bQ(u))$: the conjugate of $P(u)/Q(u)$ is a Möbius function of $P(u)/Q(u)$.
--
--   Two polynomials $P, S \in \overline{\mathbb{Q}}[X]$ of degree at most $2$ have a common zero on the projective line if they are not coprime (a common root in $\overline{\mathbb{Q}}$) or their coefficients of $X^2$ are both zero (a common zero at $\infty$, reading $P$ and $S$ as binary forms of degree $2$).
--
--   Let $\tau$ be the involution of the research notes, which exchanges the points of each fibre of $h = P/Q$, and, when $\rho = u\bar u$ is algebraic, let $\sigma$ send $f(u)$ to $\bar f(\rho/u)$, so that $\overline{h(u)} = h^\sigma(u)$. The conclusion says that $\sigma$ maps $\overline{\mathbb{Q}}(h)$ to itself, that is, $\sigma\tau\sigma = \tau$. The statement and its proof need no hypothesis on $u\bar u$. The hypothesis on common zeros is needed: for $u\bar u = 1$, $\mathrm{span}(u^{-2}, u^{-1}, 1, u, u^2)$, which is $W_A$ for $P = X^2 - X$, $Q = 1$, $S_1 = X - 1$, $S_2 = X$ (here $P$ and $S_1$ share the root $1$), is stable under conjugation, and $\overline{u^2 - u} = u^{-2} - u^{-1}$ is not a Möbius function of $u^2 - u$.
--
--   **Proof.** $W$ has dimension $5$ (`DiazModulus.invisible_two_orbit_space_u_multiplier_space_eq`, resp. `DiazModulus.invisible_cyclic_space_u_multiplier_space_eq`), so `DiazModulus.quadratic_two_orbit_space_carries_two_by_three_configuration` (10.139), resp. `DiazModulus.quadratic_cyclic_space_carries_two_by_three_configuration` (10.140), gives a configuration $(x, y)$ in $W$ with $x = (1, P(u)/Q(u))$. Complex conjugation maps $\overline{\mathbb{Q}}$ to itself, so $(\bar x, \bar y)$ is again a pair of linearly independent families, and its products lie in $W$ because $W$ is stable under conjugation. `DiazModulus.invisible_two_orbit_space_configuration_ratio_mobius`, resp. `DiazModulus.invisible_cyclic_space_configuration_ratio_mobius`, gives $\overline{P(u)/Q(u)}\,(cP(u) + dQ(u)) = aP(u) + bQ(u)$; multiply by $\overline{Q(u)} \neq 0$.
--
--   **Novelty.** None claimed; routine. It is Q1.7 of the project's research notes (R12), a short consequence of Q1.6 (`DiazModulus.invisible_two_orbit_space_configuration_ratio_mobius`, `DiazModulus.invisible_cyclic_space_configuration_ratio_mobius`).
-- source:
--   No novelty claimed. Q1.7 of the Diaz modulus mission's research notes (round R12), from Q1.6 and the configurations DiazModulus.quadratic_two_orbit_space_carries_two_by_three_configuration (10.139) and DiazModulus.quadratic_cyclic_space_carries_two_by_three_configuration (10.140). Uses DiazModulus.invisible_two_orbit_space_u_multiplier_space_eq, DiazModulus.invisible_cyclic_space_u_multiplier_space_eq, DiazModulus.quadratic_two_orbit_space_carries_two_by_three_configuration, DiazModulus.quadratic_cyclic_space_carries_two_by_three_configuration, DiazModulus.invisible_two_orbit_space_configuration_ratio_mobius and DiazModulus.invisible_cyclic_space_configuration_ratio_mobius. R21b of the Diaz modulus mission. Formal proof: Diaz modulus mission, 30 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Polynomial in
theorem conj_stable_invisible_quadratic_space_conj_ratio_mobius (u : ℂ) (hu : u ∉ Qbar) (P Q S₁ S₂ : (↥Qbar)[X])
    (hcop : IsCoprime P Q) (hdeg : max P.natDegree Q.natDegree = 2) (hS₁ : S₁.natDegree ≤ 2) (hS₂ : S₂.natDegree ≤ 2)
    (W : Submodule (↥Qbar) ℂ)
    (hform : ((IsCoprime P S₁ ∧ IsCoprime Q S₂ ∧ (P.coeff 2 ≠ 0 ∨ S₁.coeff 2 ≠ 0) ∧
        (Q.coeff 2 ≠ 0 ∨ S₂.coeff 2 ≠ 0)) ∧ W = Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P),
        aeval u P * aeval u S₂ / (u * aeval u Q)} : Set ℂ)) ∨
      ((IsCoprime P S₁ ∧ (P.coeff 2 ≠ 0 ∨ S₁.coeff 2 ≠ 0)) ∧ W = Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P),
        aeval u Q * (aeval u Q * aeval u S₁ + aeval u P * aeval u S₂) / (u * aeval u P ^ 2)} : Set ℂ)))
    (hσ : ∀ w ∈ W, conj w ∈ W) :
    ∃ a b c d : ℂ, a ∈ Qbar ∧ b ∈ Qbar ∧ c ∈ Qbar ∧ d ∈ Qbar ∧ a * d - b * c ≠ 0 ∧
      conj (aeval u P) * (c * aeval u P + d * aeval u Q) = conj (aeval u Q) * (a * aeval u P + b * aeval u Q) := by
  sorry

end DiazModulus
