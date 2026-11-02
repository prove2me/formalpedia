-- Prove2me | Theorems.Thm_DiazModulus_quadratic_space_mem_iff_numerator
-- name    : DiazModulus.quadratic_space_mem_iff_numerator
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-01T09:20:37.42631+00:00
-- url     : https://prove2.me/theorems/df8f04c7-46b4-4e83-9210-f25970689151
-- title:
--   Membership in the two-orbit and cyclic degree-two spans, written over the common denominators uPQ and uP²
-- statement:
--   Let $u \in \mathbb{C}$ be transcendental, that is, $u \notin \overline{\mathbb{Q}}$ (the algebraic numbers); spans and linear independence are over $\overline{\mathbb{Q}}$. Let $P, Q, S_1, S_2 \in \overline{\mathbb{Q}}[X]$ with $P \neq 0$ and $Q \neq 0$. Put $g_1 = Q(u)S_1(u)/(uP(u))$, $g_2 = P(u)S_2(u)/(uQ(u))$, $g_2' = Q(u)(Q(u)S_1(u) + P(u)S_2(u))/(uP(u)^2)$, $W_A = \mathrm{span}(1, u, u^{-1}, g_1, g_2)$ and $W_B = \mathrm{span}(1, u, u^{-1}, g_1, g_2')$. Then, for every $f \in \mathbb{C}$:
--
--   - $f \in W_A$ if and only if $f\,uP(u)Q(u) = (PQA + a_1Q^2S_1 + a_2P^2S_2)(u)$ for some $A \in \overline{\mathbb{Q}}[X]$ with $\deg A \leq 2$ and some $a_1, a_2 \in \overline{\mathbb{Q}}$;
--   - $f \in W_B$ if and only if $f\,uP(u)^2 = (P^2A + a_1PQS_1 + a_2Q(QS_1 + PS_2))(u)$ for some such $A, a_1, a_2$.
--
--   So membership in the two-orbit shape (D2a) and the cyclic shape (D2b) of Theorem NF (`DiazModulus.degree_two_configuration_normal_form`) becomes a polynomial identity once the denominator $uPQ$, resp. $uP^2$, is cleared. No degree hypothesis is made.
--
--   **Proof.** Both spans have the shape $\mathrm{span}(1, u, u^{-1}, g, h)$ with $g \cdot uD(u) = G(u)$ and $h \cdot uD(u) = H(u)$ for a non-zero polynomial $D$: $D = PQ$, $G = Q^2S_1$, $H = P^2S_2$ for $W_A$, and $D = P^2$, $G = PQS_1$, $H = Q(QS_1 + PS_2)$ for $W_B$; $D(u) \neq 0$ as $u$ is transcendental. Multiplied by $uD(u)$, the element $c_0 + c_1u + c_2u^{-1} + a_1g + a_2h$ becomes $(DA + a_1G + a_2H)(u)$ with $A = c_2 + c_0X + c_1X^2$, and conversely every $A$ of degree at most $2$ arises this way.
--
--   **Novelty.** None claimed; routine. It turns membership in the shapes (D2a) and (D2b) into the polynomial identities on which the divisibility arguments of the nodes on invisible degree-two spaces run.
-- source:
--   No novelty claimed. Membership in the degree-two shapes D2a and D2b of Theorem NF (DiazModulus.degree_two_configuration_normal_form, 10.138) over the common denominators. R21b of the Diaz modulus mission. Formal proof: Diaz modulus mission, 30 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Polynomial in
theorem quadratic_space_mem_iff_numerator (u : ℂ) (hu : u ∉ Qbar) (P Q S₁ S₂ : (↥Qbar)[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    (∀ f : ℂ, f ∈ Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P),
        aeval u P * aeval u S₂ / (u * aeval u Q)} : Set ℂ) ↔
      ∃ (A : (↥Qbar)[X]) (a₁ a₂ : ↥Qbar), A.natDegree ≤ 2 ∧
        f * (u * aeval u P * aeval u Q) = aeval u (P * Q * A + C a₁ * (Q ^ 2 * S₁) + C a₂ * (P ^ 2 * S₂))) ∧
    (∀ f : ℂ, f ∈ Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P),
        aeval u Q * (aeval u Q * aeval u S₁ + aeval u P * aeval u S₂) / (u * aeval u P ^ 2)} : Set ℂ) ↔
      ∃ (A : (↥Qbar)[X]) (a₁ a₂ : ↥Qbar), A.natDegree ≤ 2 ∧
        f * (u * aeval u P ^ 2) = aeval u (P ^ 2 * A + C a₁ * (P * Q * S₁) + C a₂ * (Q * (Q * S₁ + P * S₂)))) := by
  sorry

end DiazModulus
