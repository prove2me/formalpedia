-- Prove2me | Theorems.Thm_DiazModulus_degree_two_configuration_pencil_normal_form
-- name    : DiazModulus.degree_two_configuration_pencil_normal_form
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-01T09:19:59.470198+00:00
-- url     : https://prove2.me/theorems/d269dc53-2efb-4a0b-a122-6077ef47d2ba
-- title:
--   Theorem NF with the pencil kept: the normal form of a degree-two configuration uses an invertible combination (P′, Q′) of its own ratio's pair (p, q)
-- statement:
--   Let $u \in \mathbb{C}$ be transcendental, that is, $u \notin \overline{\mathbb{Q}}$ (the algebraic numbers); spans and linear independence are over $\overline{\mathbb{Q}}$. Let $W \subseteq \mathbb{C}$ be a $\overline{\mathbb{Q}}$-vector subspace of dimension $5$ with $1, u, u^{-1} \in W$, that is, $H_0 \subseteq W$ for $H_0 = \mathrm{span}(1, u, u^{-1})$. Let $x_0, x_1 \in \mathbb{C}$ be linearly independent and $y_0, y_1, y_2 \in \mathbb{C}$ linearly independent, with $x_iy_j \in W$ for all $i, j$ (a $2 \times 3$ configuration in $W$). Let $p, q \in \overline{\mathbb{Q}}[X]$ be coprime with $\max(\deg p, \deg q) = 2$, and suppose $x_1q(u) = x_0p(u)$, so that the ratio $x_1/x_0$ is $p(u)/q(u)$. Then there are $a, b, c, d \in \overline{\mathbb{Q}}$ with $ad - bc \neq 0$ such that, for $P' = ap + bq$ and $Q' = cp + dq$, one of the following holds:
--
--   - **(scalar)** $Q'(u)R(u)/(uP'(u)) \in W$ for every $R \in \overline{\mathbb{Q}}[X]$ of degree at most $2$;
--   - **(D2a, two-orbit)** $W = \mathrm{span}(1, u, u^{-1}, Q'(u)S_1(u)/(uP'(u)), P'(u)S_2(u)/(uQ'(u)))$ for some $S_1, S_2 \in \overline{\mathbb{Q}}[X]$ of degree at most $2$;
--   - **(D2b, cyclic)** $W = \mathrm{span}(1, u, u^{-1}, Q'(u)S_1(u)/(uP'(u)), Q'(u)(Q'(u)S_1(u) + P'(u)S_2(u))/(uP'(u)^2))$ for some such $S_1, S_2$.
--
--   This is Theorem NF (`DiazModulus.degree_two_configuration_normal_form`) with the pencil kept. There the pencil of the conclusion is quantified afresh; here it is an invertible combination of the pair $(p, q)$ of the configuration, so $P'(u)/Q'(u)$ is a Möbius function of the ratio $x_1/x_0$. The scalar case is kept as such.
--
--   **Proof.** As in Theorem NF: $x_0 \neq 0$ and $q(u) \neq 0$, and $y' = x_0y$ is a linearly independent triple with $y'_j \in W$ and $(p(u)/q(u))y'_j \in W$. `DiazModulus.degree_two_configuration_multiplier_complement` (10.134) gives $\lambda \in \{0, 1, 2\}$ and $g_1, g_2$ with $W = \mathrm{span}(1, u, u^{-1}, g_1, g_2)$ and $kg_j \in W$ for $k = q(u)/E(u)$, $E = p - \lambda q$. The pencil $(q, E)$ is coprime of maximal degree $2$ (`DiazModulus.coprime_pencil_mobius`, 10.130), and `DiazModulus.quadratic_complement_eigen_forms` (10.136) gives three cases, all with denominators $q - cE$. Scalar and cyclic: $P' = q - cE = -cp + (1 + c\lambda)q$ and $Q' = E = p - \lambda q$, of determinant $-1$, and the shapes are already the target ones. Two-orbit ($c_1 \neq c_2$): $P' = q - c_1E$ and $Q' = q - c_2E$, of determinant $c_2 - c_1$. Since $P' - Q' = (c_2 - c_1)E$, the generators $E(u)R_1(u)/(uP'(u))$ and $E(u)R_2(u)/(uQ'(u))$ differ from $Q'(u)S_1(u)/(uP'(u))$ and $P'(u)S_2(u)/(uQ'(u))$, where $S_1 = -R_1/(c_2 - c_1)$ and $S_2 = R_2/(c_2 - c_1)$, by $S_1(u)/u$ and $S_2(u)/u$, which lie in $H_0$; so the two spans agree.
--
--   **Novelty.** None claimed; routine. It re-assembles the proof of Theorem NF (`DiazModulus.degree_two_configuration_normal_form`, 10.138; Theorem 2 of the project's research notes (R12)) from `DiazModulus.degree_two_configuration_multiplier_complement` and `DiazModulus.quadratic_complement_eigen_forms` so that the pencil is recorded; the Q1.6 nodes `DiazModulus.invisible_two_orbit_space_configuration_ratio_mobius` and `DiazModulus.invisible_cyclic_space_configuration_ratio_mobius` need it.
-- source:
--   No novelty claimed. Theorem NF (DiazModulus.degree_two_configuration_normal_form, 10.138; Theorem 2 of the Diaz modulus mission's research notes (round R12)) with the pencil recorded, re-assembled from DiazModulus.degree_two_configuration_multiplier_complement (10.134) and DiazModulus.quadratic_complement_eigen_forms (10.136). Uses DiazModulus.degree_two_configuration_multiplier_complement, DiazModulus.coprime_pencil_mobius and DiazModulus.quadratic_complement_eigen_forms. R21b of the Diaz modulus mission. Formal proof: Diaz modulus mission, 30 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Polynomial in
theorem degree_two_configuration_pencil_normal_form (u : ℂ) (hu : u ∉ Qbar) (W : Submodule (↥Qbar) ℂ) [FiniteDimensional (↥Qbar) W]
    (hW : Module.finrank (↥Qbar) W = 5) (h1 : (1 : ℂ) ∈ W) (hu1 : u ∈ W) (hui : u⁻¹ ∈ W)
    (x : Fin 2 → ℂ) (y : Fin 3 → ℂ) (hx : LinearIndependent (↥Qbar) x)
    (hy : LinearIndependent (↥Qbar) y) (hxy : ∀ i j, x i * y j ∈ W)
    (p q : (↥Qbar)[X]) (hcop : IsCoprime p q) (hdeg : max p.natDegree q.natDegree = 2)
    (hpq : x 1 * aeval u q = x 0 * aeval u p) :
    ∃ a b c d : ↥Qbar, a * d - b * c ≠ 0 ∧
      ((∀ R : (↥Qbar)[X], R.natDegree ≤ 2 →
          aeval u (C c * p + C d * q) * aeval u R / (u * aeval u (C a * p + C b * q)) ∈ W) ∨
       (∃ S₁ S₂ : (↥Qbar)[X], S₁.natDegree ≤ 2 ∧ S₂.natDegree ≤ 2 ∧
          W = Submodule.span Qbar ({1, u, u⁻¹, aeval u (C c * p + C d * q) * aeval u S₁ / (u * aeval u (C a * p + C b * q)),
            aeval u (C a * p + C b * q) * aeval u S₂ / (u * aeval u (C c * p + C d * q))} : Set ℂ)) ∨
       (∃ S₁ S₂ : (↥Qbar)[X], S₁.natDegree ≤ 2 ∧ S₂.natDegree ≤ 2 ∧
          W = Submodule.span Qbar ({1, u, u⁻¹, aeval u (C c * p + C d * q) * aeval u S₁ / (u * aeval u (C a * p + C b * q)),
            aeval u (C c * p + C d * q) * (aeval u (C c * p + C d * q) * aeval u S₁ + aeval u (C a * p + C b * q) * aeval u S₂) /
              (u * aeval u (C a * p + C b * q) ^ 2)} : Set ℂ))) := by
  sorry

end DiazModulus
