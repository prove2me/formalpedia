-- Prove2me | Theorems.Thm_DiazModulus_laurent_involution_class_space_cyclic_form
-- name    : DiazModulus.laurent_involution_class_space_cyclic_form
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-23T11:54:54.990685+00:00
-- url     : https://prove2.me/theorems/00e48e2c-49f1-4fe9-822b-495d0b8e830a
-- title:
--   The span of Theorem E's involution class, span(1, u, ū, v̄² + e v², β v̄³ + ζ v² + e v³) with v = u/s, is Theorem F's cyclic space D2b for the pencil (s X, X² + β s²)
-- statement:
--   Let $u \in \mathbb{C}$ be transcendental, that is, $u \notin \overline{\mathbb{Q}}$ (the algebraic numbers); spans and linear independence are over $\overline{\mathbb{Q}}$. Let $s \in \overline{\mathbb{Q}}$ with $s^2 = u\bar u$, put $v = u/s$, and let $e, \beta, \zeta \in \overline{\mathbb{Q}}$ with $\beta \neq 0$. Then there are $P', Q', S_1, S_2 \in \overline{\mathbb{Q}}[X]$ with $P'(u) = su$, $Q'(u) = u^2 + \beta s^2$, $S_1(u) = s/\beta + (e/s)u^2$ and $S_2(u) = (\zeta/s)u^2$, such that $P', Q'$ are coprime, $\max(\deg P', \deg Q') = 2$, $\deg S_1, \deg S_2 \leq 2$, and $\mathrm{span}(1, u, \bar u, \bar v^2 + ev^2, \beta\bar v^3 + \zeta v^2 + ev^3) = \mathrm{span}(1, u, u^{-1}, Q'(u)S_1(u)/(uP'(u)), Q'(u)(Q'(u)S_1(u) + P'(u)S_2(u))/(uP'(u)^2))$.
--
--   The left side is the space of Theorem E's involution class (Q), which asks in addition $e\bar e = 1$, $\beta\bar\beta = 1$ and $\zeta = -\beta e^2\bar\zeta$; the identity needs none of these, and no dimension hypothesis. So every hull of class (Q) has Theorem F's shape (D2b), with $P' = sX$ and $Q' = X^2 + \beta s^2$.
--
--   **Proof.** As $u \neq 0$, $s \neq 0$; and $s$ is real, since $s^2 = u\bar u = |u|^2 > 0$. So $\bar u = s^2/u$ and $\bar v = s/u$. Take $P' = sX$ and $Q' = X^2 + \beta s^2$, coprime by the Bézout identity $-(\beta s^3)^{-1}X\cdot P' + (\beta s^2)^{-1}Q' = 1$, with $\max(\deg P', \deg Q') = 2$; and $S_1 = s/\beta + (e/s)X^2$, $S_2 = (\zeta/s)X^2$. Write $n_0 = \bar v^2 + ev^2$, $n_1 = \beta\bar v^3 + \zeta v^2 + ev^3$, $g_1 = Q'(u)S_1(u)/(uP'(u))$ and $g_2 = Q'(u)(Q'(u)S_1(u) + P'(u)S_2(u))/(uP'(u)^2)$. Two exact identities hold: $g_1 - n_0 = \beta e + \beta^{-1}$ and $g_2 - n_1 = \beta\zeta + ((2\beta e + \beta^{-1})/s)\,u + ((\beta^2e + 2)/s)\,\bar u$. With $\bar u = s^2u^{-1}$ and $u^{-1} = s^{-2}\bar u$, each generator of either span is an explicit $\overline{\mathbb{Q}}$-combination of the generators of the other, and the two inclusions are checked by field arithmetic. No dimension or independence argument is used, and none of the constraints $e\bar e = \beta\bar\beta = 1$, $\zeta = -\beta e^2\bar\zeta$ of class (Q).
--
--   **Novelty.** Not found in the sources read; routine. An identity of spans that writes Theorem E's involution class (Q) in the coordinates of Theorem F: every hull of class (Q) has shape (D2b), with the pencil $(sX, X^2 + \beta s^2)$, whose ratio $Q'(u)/P'(u) = (u + \beta\bar u)/s$ is that of the configuration of class (Q). That configuration is in print: the proof of Diaz (2004, Théorème 2), at $x = (1, (u + \beta\bar u)/s)$; also Diaz (2007, Théorème 4(1)).
-- source:
--   Not found in the sources read. Theorem E's involution class (Q) (DiazModulus.laurent_conj_hull_two_by_three_configuration_iff) in the coordinates of Theorem F (DiazModulus.rational_conj_hull_two_by_three_configuration_iff). The configuration of class (Q) is in print: the proof of G. Diaz, Utilisation de la conjugaison complexe dans l'étude de la transcendance de valeurs de la fonction exponentielle usuelle, J. Théor. Nombres Bordeaux 16 (2004), 535–553, Théorème 2, at x = (1, (u + βū)/s); also G. Diaz, Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques : conjectures et résultats partiels, J. Théor. Nombres Bordeaux 19 (2007), 373–391, Théorème 4(1). R21a of the Diaz modulus mission. Formal proof: Diaz modulus mission, 23 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Polynomial in
theorem laurent_involution_class_space_cyclic_form (u s : ℂ) (hu : u ∉ Qbar) (hs : s ∈ Qbar) (hss : s * s = u * conj u)
    (e β ζ : ℂ) (he : e ∈ Qbar) (hβ : β ∈ Qbar) (hζ : ζ ∈ Qbar) (hβ0 : β ≠ 0) :
    ∃ P' Q' S₁ S₂ : (↥Qbar)[X], aeval u P' = s * u ∧ aeval u Q' = u ^ 2 + β * s ^ 2 ∧
      aeval u S₁ = s / β + e / s * u ^ 2 ∧ aeval u S₂ = ζ / s * u ^ 2 ∧
      IsCoprime P' Q' ∧ max P'.natDegree Q'.natDegree = 2 ∧ S₁.natDegree ≤ 2 ∧ S₂.natDegree ≤ 2 ∧
      Submodule.span Qbar ({1, u, conj u, conj (u / s) ^ 2 + e * (u / s) ^ 2, β * conj (u / s) ^ 3 + ζ * (u / s) ^ 2 + e * (u / s) ^ 3} : Set ℂ) =
        Submodule.span Qbar ({1, u, u⁻¹, aeval u Q' * aeval u S₁ / (u * aeval u P'),
          aeval u Q' * (aeval u Q' * aeval u S₁ + aeval u P' * aeval u S₂) / (u * aeval u P' ^ 2)} : Set ℂ) := by
  sorry

end DiazModulus
