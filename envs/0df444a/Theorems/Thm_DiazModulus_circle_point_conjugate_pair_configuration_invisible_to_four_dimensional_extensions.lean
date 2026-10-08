-- Prove2me | Theorems.Thm_DiazModulus_circle_point_conjugate_pair_configuration_invisible_to_four_dimensional_extensions
-- name    : DiazModulus.circle_point_conjugate_pair_configuration_invisible_to_four_dimensional_extensions
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-06T07:47:55.008097+00:00
-- url     : https://prove2.me/theorems/901396cf-2688-4738-be1c-a80b6ff6e7c7
-- title:
--   For the same u, a and z, W = Q̄ + Q̄u + Q̄ū + Q̄z + Q̄z̄ carries a 2×3 configuration, while no Q̄ + Q̄u + Q̄ū + Q̄w with w ∈ W outside Q̄ + Q̄u + Q̄ū does
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ with $\rho = u\bar u$ algebraic, let $a \in \overline{\mathbb{Q}}$, $a \neq 0$, and let $z$ be $u/(u^2 - a)$ if $a\bar a \neq \rho^2$, or $u/(u^2 - a)^2$ if $a\bar a = \rho^2$. Put $H_0 = \overline{\mathbb{Q}} + \overline{\mathbb{Q}}u + \overline{\mathbb{Q}}\bar u$ and $W = H_0 + \overline{\mathbb{Q}}z + \overline{\mathbb{Q}}\bar z$. Then $W$ carries a $2 \times 3$ configuration: $x_1, x_2$ independent over $\overline{\mathbb{Q}}$ and $y_1, y_2, y_3$ independent over $\overline{\mathbb{Q}}$ with all six products $x_iy_j$ in $W$. But for no $w \in W$ outside $H_0$ does $H_0 + \overline{\mathbb{Q}}w$ carry one.
--
--   So the configuration is invisible to Theorem B's four-dimensional spaces. It does not need all of $W$: its six products span the odd part $\overline{\mathbb{Q}}u + \overline{\mathbb{Q}}\bar u + \overline{\mathbb{Q}}z + \overline{\mathbb{Q}}\bar z$, which does not contain $1$. Since $\widetilde{\mathcal{L}}$ is closed under complex conjugation, a hypothesis $z \in \widetilde{\mathcal{L}}$ brings $\bar z$ with it, so $W$ is the space Roy's strong six exponentials theorem sees at a candidate; `DiazModulus.circle_point_extension_two_by_three_configuration_iff` (Theorem B) treats the four-dimensional spaces $H_0 + \overline{\mathbb{Q}}w$ only. The statement does not involve $e^u$, so it keeps its content if Diaz's conjecture holds.
--
--   **Proof.** The configuration is `DiazModulus.circle_point_conjugate_pair_extension_carries_two_by_three_configuration`. Let $w \in W \setminus H_0$ and suppose $H_0 + \overline{\mathbb{Q}}w$ carries one. By Theorem B, $w \in H_0 + \overline{\mathbb{Q}}t$ for $t$ one of $u^2$, $\bar u^2$, $1/(u - b)$ with $b$ algebraic and non-zero. Since $w \notin H_0$, exchange gives $t \in H_0 + \overline{\mathbb{Q}}w \subseteq W$, which `DiazModulus.circle_point_conjugate_pair_extension_excludes_squares_and_reciprocals` rules out.
--
--   **Novelty.** Not found in the sources read; it is short (parity plus Theorem B). With the strong six exponentials theorem, the configuration gives at a candidate exclusions that are already one substitution in Diaz (2004, Th. 2) and Diaz (2007, Th. 6(3)): `DiazModulus.candidate_div_sq_sub_not_mem_logAlgTilde`.
-- source:
--   That no four-dimensional subspace containing Q̄ + Q̄u + Q̄ū carries a configuration was not found in the sources read; the configuration has the shape of those in the proofs of G. Diaz, Utilisation de la conjugaison complexe dans l'étude de la transcendance de valeurs de la fonction exponentielle usuelle, J. Théor. Nombres Bordeaux 16 (2004), 535–553, Th. 2 (p. 538), and of G. Diaz, Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques : conjectures et résultats partiels, J. Théor. Nombres Bordeaux 19 (2007), 373–391, Th. 6(1) and 7(1) (pp. 389–390). Uses DiazModulus.circle_point_extension_two_by_three_configuration_iff (Theorem B of the Diaz modulus mission). Formal proof: Diaz modulus mission, 6 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem circle_point_conjugate_pair_configuration_invisible_to_four_dimensional_extensions (u a z : ℂ)
    (hu : u ∉ Qbar) (hρ : IsAlgebraic ℚ (u * conj u)) (ha : a ∈ Qbar) (ha0 : a ≠ 0)
    (hz : (a * conj a ≠ (u * conj u) ^ 2 ∧ z = u / (u ^ 2 - a)) ∨
      (a * conj a = (u * conj u) ^ 2 ∧ z = u / (u ^ 2 - a) ^ 2)) :
    (∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
        ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ)) ∧
      ∀ w ∈ Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ),
        w ∉ Submodule.span Qbar ({1, u, conj u} : Set ℂ) →
        ¬ ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧
          LinearIndependent (↥Qbar) y ∧
          ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, w} : Set ℂ) := by
  sorry

end DiazModulus
