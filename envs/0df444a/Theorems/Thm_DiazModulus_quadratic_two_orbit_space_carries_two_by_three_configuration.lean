-- Prove2me | Theorems.Thm_DiazModulus_quadratic_two_orbit_space_carries_two_by_three_configuration
-- name    : DiazModulus.quadratic_two_orbit_space_carries_two_by_three_configuration
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-23T07:20:03.680416+00:00
-- url     : https://prove2.me/theorems/6f7c9c8b-9076-47b4-adfd-ae93344540d0
-- title:
--   Every five-dimensional span(1, u, u⁻¹, QR₁/(uP), PR₂/(uQ)) with P/Q of degree 2 carries the configuration (1, P/Q) ⊗ (Q/u, R₂/u, QR₁/(uP))
-- statement:
--   Let $u \in \mathbb{C}$ be transcendental, that is, $u \notin \overline{\mathbb{Q}}$ (the algebraic numbers); spans and linear independence are over $\overline{\mathbb{Q}}$. Let $P, Q, R_1, R_2 \in \overline{\mathbb{Q}}[X]$ with $\max(\deg P, \deg Q) = 2$ and $\deg R_1, \deg R_2 \leq 2$, and suppose $W = \mathrm{span}(1, u, u^{-1}, Q(u)R_1(u)/(uP(u)), P(u)R_2(u)/(uQ(u)))$ has dimension $5$. Then $x = (1, P(u)/Q(u))$ and $y = (Q(u)/u, R_2(u)/u, Q(u)R_1(u)/(uP(u)))$ are each linearly independent, and $x_iy_j \in W$ for all $i, j$.
--
--   So every five-dimensional space of shape (D2a) carries a $2 \times 3$ configuration with ratio $P(u)/Q(u)$. $P$ and $Q$ need not be coprime.
--
--   **Proof.** Write $g_1 = Q(u)R_1(u)/(uP(u))$ and $g_2 = P(u)R_2(u)/(uQ(u))$. As $W$ has dimension $5$, the family $1, u, u^{-1}, g_1, g_2$ is independent; in particular $g_1, g_2 \neq 0$, so $P(u), Q(u) \neq 0$. Every $R(u)/u$ with $\deg R \leq 2$ lies in $H_0$, so a relation $R(u)/u + ag_1 + bg_2 = 0$ forces $a = b = 0$ and $R(u) = 0$. The products are explicit (values at $u$): $(P/Q)(Q/u) = P/u$, $(P/Q)(R_2/u) = g_2$, $(P/Q)g_1 = R_1/u$, and the row $1$ gives $Q/u, R_2/u, g_1$. Independence of $x$: multiplying $a + bP/Q = 0$ by $R_2/u$ gives $aR_2/u + bg_2 = 0$, so $b = 0$, then $a = 0$. Independence of $y$: the coefficient of $g_1$ in a relation vanishes; multiplying the relation by $P/Q$ gives $(aP + cR_1)/u + bg_2 = 0$, so $b = 0$; then $aQ(u)/u = 0$ gives $a = 0$. No transcendence is used beyond $u \neq 0$.
--
--   **Novelty.** Not found in the sources read; routine. Explicit identities: the existence of a configuration is the easy direction; the classification is Theorem NF (`DiazModulus.degree_two_configuration_normal_form`).
-- source:
--   Not found in the sources read. The space is the two-orbit normal form of the mission's research notes (round R12, Q1.3), there in the coordinate h − c. R20 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 23 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Polynomial in
theorem quadratic_two_orbit_space_carries_two_by_three_configuration (u : ℂ) (hu : u ∉ Qbar)
    (P Q R₁ R₂ : (↥Qbar)[X]) (hdeg : max P.natDegree Q.natDegree = 2)
    (hR₁ : R₁.natDegree ≤ 2) (hR₂ : R₂.natDegree ≤ 2)
    (h5 : Module.finrank (↥Qbar) (Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u R₁ / (u * aeval u P),
        aeval u P * aeval u R₂ / (u * aeval u Q)} : Set ℂ)) = 5) :
    LinearIndependent (↥Qbar) ![1, aeval u P / aeval u Q] ∧
    LinearIndependent (↥Qbar) ![aeval u Q / u, aeval u R₂ / u, aeval u Q * aeval u R₁ / (u * aeval u P)] ∧
    ∀ i j, ![1, aeval u P / aeval u Q] i *
      ![aeval u Q / u, aeval u R₂ / u, aeval u Q * aeval u R₁ / (u * aeval u P)] j ∈
      Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u R₁ / (u * aeval u P),
        aeval u P * aeval u R₂ / (u * aeval u Q)} : Set ℂ) := by
  sorry

end DiazModulus
