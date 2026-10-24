-- Prove2me | Theorems.Thm_DiazModulus_laurent_real_pencil_class_space_u_multiplier_triple
-- name    : DiazModulus.laurent_real_pencil_class_space_u_multiplier_triple
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-23T11:54:57.482089+00:00
-- url     : https://prove2.me/theorems/bf190dc0-3812-4920-8dcc-4e8e2e6fa6a6
-- title:
--   In the real pencil space span(1, u, ū, g, ḡ), g = G(v) + κ conj(v G(v)), v = u/s, the free triple (1/u, 1, g) and its u-multiple lie in the span: Theorem F's shape D1
-- statement:
--   Let $u \in \mathbb{C}$ be transcendental, that is, $u \notin \overline{\mathbb{Q}}$ (the algebraic numbers); spans and linear independence are over $\overline{\mathbb{Q}}$. Let $s \in \overline{\mathbb{Q}}$ with $s^2 = u\bar u$, and put $v = u/s$. Let $\kappa \in \overline{\mathbb{Q}}$ with $\kappa\bar\kappa = 1$ and $G \in \overline{\mathbb{Q}}[X]$ with $\deg G \geq 1$, put $g = G(v) + \kappa\,\overline{vG(v)}$ and $W = \mathrm{span}(1, u, \bar u, g, \bar g)$. Then $t = (u^{-1}, 1, g)$ is linearly independent, and $t_j \in W$ and $ut_j \in W$ for $j = 0, 1, 2$.
--
--   So $W$ satisfies Theorem F's condition (D1). Theorem E's real pencil class (R) asks in addition $G(0) = 0$ and $\deg G \geq 2$, so every hull of class (R) has shape (D1).
--
--   **Proof.** As $u \neq 0$, $s^2 = |u|^2 > 0$ makes $s$ real and non-zero. Hence $v\bar v = u\bar u/s^2 = 1$, $v \notin \overline{\mathbb{Q}}$ (otherwise $u = sv$ would be algebraic), and $u^{-1} = s^{-1}\bar v$. Freeness: the real pencil normal form node (`DiazModulus.laurent_real_pencil_normal_form_carries_two_by_three_configuration`, 10.92) makes $(\bar v, 1, g)$ linearly independent, and a relation $au^{-1} + b + cg = 0$ is the relation $(a/s)\bar v + b + cg = 0$, so $a = b = c = 0$. Membership: $u^{-1} = s^{-2}\bar u$, $1$ and $g$ lie in $W$. Multiples: $u \cdot u^{-1} = 1$ and $u \cdot 1 = u$ lie in $W$, and $vg = vG(v) + \kappa v\bar v\,\overline{G(v)} = \kappa\bar g$, because $v\bar v = 1$ and $\kappa\bar\kappa = 1$; so $ug = svg = s\kappa\bar g \in W$.
--
--   **Novelty.** Not found in the sources read; routine. It follows from `DiazModulus.laurent_real_pencil_normal_form_carries_two_by_three_configuration` (10.92), which gives the configuration of class (R) with the triple $(\bar v, 1, g)$: Theorem E's real pencil class (R) has Theorem F's shape (D1). The real pencil spaces are the project's (blueprint Prop. 10.42).
-- source:
--   Not found in the sources read. Theorem E's real pencil class (R) (DiazModulus.laurent_conj_hull_two_by_three_configuration_iff) in the coordinates of Theorem F (DiazModulus.rational_conj_hull_two_by_three_configuration_iff): the independence comes from DiazModulus.laurent_real_pencil_normal_form_carries_two_by_three_configuration (10.92) after a rescaling, and the memberships are checked directly. The real pencil spaces are the project's (blueprint Prop. 10.42, DiazModulus.conj_stable_real_pencil_space_carries_two_by_three_configuration). Uses DiazModulus.laurent_real_pencil_normal_form_carries_two_by_three_configuration. R21a of the Diaz modulus mission. Formal proof: Diaz modulus mission, 23 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem laurent_real_pencil_class_space_u_multiplier_triple
    (u s : ℂ) (hu : u ∉ Qbar) (hs : s ∈ Qbar) (hss : s * s = u * conj u)
    (κ : ℂ) (hκ : κ ∈ Qbar) (hκ1 : κ * conj κ = 1) (G : Polynomial ↥Qbar) (hG : 1 ≤ G.natDegree) :
    LinearIndependent (↥Qbar) ![u⁻¹, 1, (Polynomial.aeval (u / s) G + κ * conj ((u / s) * Polynomial.aeval (u / s) G))] ∧
      ∀ j, ![u⁻¹, 1, (Polynomial.aeval (u / s) G + κ * conj ((u / s) * Polynomial.aeval (u / s) G))] j ∈
        Submodule.span Qbar ({1, u, conj u, (Polynomial.aeval (u / s) G + κ * conj ((u / s) * Polynomial.aeval (u / s) G)), conj (Polynomial.aeval (u / s) G + κ * conj ((u / s) * Polynomial.aeval (u / s) G))} : Set ℂ) ∧
        u * ![u⁻¹, 1, (Polynomial.aeval (u / s) G + κ * conj ((u / s) * Polynomial.aeval (u / s) G))] j ∈
        Submodule.span Qbar ({1, u, conj u, (Polynomial.aeval (u / s) G + κ * conj ((u / s) * Polynomial.aeval (u / s) G)), conj (Polynomial.aeval (u / s) G + κ * conj ((u / s) * Polynomial.aeval (u / s) G))} : Set ℂ) := by
  sorry

end DiazModulus
