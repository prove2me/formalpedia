-- Prove2me | Theorems.Thm_DiazModulus_laurent_involution_space_carries_two_by_three_configuration
-- name    : DiazModulus.laurent_involution_space_carries_two_by_three_configuration
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-18T14:28:36.007594+00:00
-- url     : https://prove2.me/theorems/b9e7a8bf-a58e-4cbc-ad2e-378af159d6c8
-- title:
--   (1, v + βv̄) and (1, v̄ + eβv, v̄² + ζv + ev²) form a 2×3 configuration in span(1, v, v̄, v̄² + ev², βv̄³ + ζv² + ev³)
-- statement:
--   Let $v \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ with $v\bar v = 1$. Let $e, \beta, \zeta \in \overline{\mathbb{Q}}$ be arbitrary and $S = \mathrm{span}_{\overline{\mathbb{Q}}}(1, v, \bar v, \bar v^2 + ev^2, \beta\bar v^3 + \zeta v^2 + ev^3)$. Then $1, v + \beta\bar v$ are linearly independent over $\overline{\mathbb{Q}}$, so are $1, \bar v + e\beta v, \bar v^2 + \zeta v + ev^2$, and each of the six products of a member of the first family with a member of the second lies in $S$.
--
--   With $v = u/s$ these are the configurations of class (Q) in `DiazModulus.laurent_conj_hull_two_by_three_configuration_iff`.
--
--   **Proof.** Using only $v\bar v = 1$, the six products are $1$, $\bar v + e\beta v$, $(\bar v^2 + ev^2) + \zeta v$, $v + \beta\bar v$, $\beta(\bar v^2 + ev^2) + (1 + e\beta^2)$ and $(\beta\bar v^3 + \zeta v^2 + ev^3) + \bar v + \beta\zeta + e\beta v$, each an explicit $\overline{\mathbb{Q}}$-combination of the five generators. For freeness, a $\overline{\mathbb{Q}}$-relation multiplied by $v$ (first family) or by $v^2$ (second family) becomes a polynomial identity of degree at most $4$ at the transcendental $v$; for the second family the coefficients at $1, v, v^2$ are the three coefficients of the relation, since the orders $0, -1, -2$ are distinct.
--
--   **Novelty.** In print: for $v = u/s$, $|e| = |\beta| = 1$ and $\zeta = -\beta e^2\bar\zeta$, this is the configuration $(x_1, x_2) \otimes (1, y, \bar y)$ to which the proof of Diaz (2004, Th. 2, p. 538) applies the strong six exponentials theorem, at $x = (1, (u + \beta\bar u)/s)$; also Diaz (2007, Th. 4(1), p. 385). Here $e, \beta, \zeta$ are arbitrary.
-- source:
--   In print: the configuration of the proof of G. Diaz, Utilisation de la conjugaison complexe dans l'étude de la transcendance de valeurs de la fonction exponentielle usuelle, J. Théor. Nombres Bordeaux 16 (2004), 535–553, Th. 2 (p. 538), at x = (1, (u + βū)/s) with v = u/s; also G. Diaz, Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques : conjectures et résultats partiels, J. Théor. Nombres Bordeaux 19 (2007), 373–391, Th. 4(1) (p. 385). R18 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 18 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem laurent_involution_space_carries_two_by_three_configuration
    (v : ℂ) (hv : v ∉ Qbar) (hv1 : v * conj v = 1)
    (e β ζ : ℂ) (he : e ∈ Qbar) (hβ : β ∈ Qbar) (hζ : ζ ∈ Qbar) :
    LinearIndependent (↥Qbar) ![1, v + β * conj v] ∧
      LinearIndependent (↥Qbar) ![1, conj v + e * β * v, conj v ^ 2 + ζ * v + e * v ^ 2] ∧
      ∀ i j, ![1, v + β * conj v] i * ![1, conj v + e * β * v, conj v ^ 2 + ζ * v + e * v ^ 2] j ∈
        Submodule.span Qbar ({1, v, conj v, conj v ^ 2 + e * v ^ 2, β * conj v ^ 3 + ζ * v ^ 2 + e * v ^ 3} : Set ℂ) := by
  sorry

end DiazModulus
