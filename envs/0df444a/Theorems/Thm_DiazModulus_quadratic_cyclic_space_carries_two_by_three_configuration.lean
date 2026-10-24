-- Prove2me | Theorems.Thm_DiazModulus_quadratic_cyclic_space_carries_two_by_three_configuration
-- name    : DiazModulus.quadratic_cyclic_space_carries_two_by_three_configuration
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-23T07:19:43.856767+00:00
-- url     : https://prove2.me/theorems/258209f7-bad0-4368-9359-c8e165705359
-- title:
--   Every five-dimensional span(1, u, u⁻¹, QR₁/(uP), Q(QR₁ + PR₂)/(uP²)) with P/Q of degree 2 carries a 2×3 configuration with ratio P/Q
-- statement:
--   Let $u \in \mathbb{C}$ be transcendental, that is, $u \notin \overline{\mathbb{Q}}$ (the algebraic numbers); spans and linear independence are over $\overline{\mathbb{Q}}$. Let $P, Q, R_1, R_2 \in \overline{\mathbb{Q}}[X]$ with $\max(\deg P, \deg Q) = 2$ and $\deg R_1, \deg R_2 \leq 2$, put $g_1 = Q(u)R_1(u)/(uP(u))$ and $g_2 = Q(u)(Q(u)R_1(u) + P(u)R_2(u))/(uP(u)^2)$, and suppose $W = \mathrm{span}(1, u, u^{-1}, g_1, g_2)$ has dimension $5$. Then $x = (1, P(u)/Q(u))$ and $y = (Q(u)/u, g_1, g_2)$ are each linearly independent, and $x_iy_j \in W$ for all $i, j$.
--
--   So every five-dimensional space of shape (D2b) carries a $2 \times 3$ configuration with ratio $P(u)/Q(u)$. $P$ and $Q$ need not be coprime.
--
--   **Proof.** Write $g_1 = Q(u)R_1(u)/(uP(u))$ and $g_2 = Q(u)(Q(u)R_1(u) + P(u)R_2(u))/(uP(u)^2)$. As $W$ has dimension $5$, the family $1, u, u^{-1}, g_1, g_2$ is independent; in particular $g_1 \neq 0$, so $P(u), Q(u) \neq 0$. Every $R(u)/u$ with $\deg R \leq 2$ lies in $H_0$, so a relation $R(u)/u + ag_1 + bg_2 = 0$ forces $a = b = 0$ and $R(u) = 0$. The products are explicit (values at $u$): $(P/Q)(Q/u) = P/u$, $(P/Q)g_1 = R_1/u$ and $(P/Q)g_2 = g_1 + R_2/u$, while the row $1$ gives $Q/u, g_1, g_2$. Independence of $x$: multiplying $a + bP/Q = 0$ by $g_2$ gives $bR_2/u + bg_1 + ag_2 = 0$, so $a = b = 0$. Independence of $y$: a relation reads $aQ(u)/u + bg_1 + cg_2 = 0$, so $b = c = 0$ and $aQ(u) = 0$, whence $a = 0$. No transcendence is used beyond $u \neq 0$.
--
--   **Novelty.** Not found in the sources read; routine. Explicit identities: the existence of a configuration is the easy direction; the classification is Theorem NF (`DiazModulus.degree_two_configuration_normal_form`).
-- source:
--   Not found in the sources read. The space is the cyclic normal form of the mission's research notes (round R12, Q1.3), there in the coordinate h − c. R20 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 23 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Polynomial in
theorem quadratic_cyclic_space_carries_two_by_three_configuration (u : ℂ) (hu : u ∉ Qbar)
    (P Q R₁ R₂ : (↥Qbar)[X]) (hdeg : max P.natDegree Q.natDegree = 2)
    (hR₁ : R₁.natDegree ≤ 2) (hR₂ : R₂.natDegree ≤ 2)
    (h5 : Module.finrank (↥Qbar) (Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u R₁ / (u * aeval u P),
        aeval u Q * (aeval u Q * aeval u R₁ + aeval u P * aeval u R₂) / (u * aeval u P ^ 2)} : Set ℂ)) = 5) :
    LinearIndependent (↥Qbar) ![1, aeval u P / aeval u Q] ∧
    LinearIndependent (↥Qbar) ![aeval u Q / u, aeval u Q * aeval u R₁ / (u * aeval u P),
      aeval u Q * (aeval u Q * aeval u R₁ + aeval u P * aeval u R₂) / (u * aeval u P ^ 2)] ∧
    ∀ i j, ![1, aeval u P / aeval u Q] i *
      ![aeval u Q / u, aeval u Q * aeval u R₁ / (u * aeval u P),
        aeval u Q * (aeval u Q * aeval u R₁ + aeval u P * aeval u R₂) / (u * aeval u P ^ 2)] j ∈
      Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u R₁ / (u * aeval u P),
        aeval u Q * (aeval u Q * aeval u R₁ + aeval u P * aeval u R₂) / (u * aeval u P ^ 2)} : Set ℂ) := by
  sorry

end DiazModulus
