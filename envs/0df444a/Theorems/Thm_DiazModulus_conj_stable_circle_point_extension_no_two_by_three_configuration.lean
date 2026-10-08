-- Prove2me | Theorems.Thm_DiazModulus_conj_stable_circle_point_extension_no_two_by_three_configuration
-- name    : DiazModulus.conj_stable_circle_point_extension_no_two_by_three_configuration
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-06T07:48:19.906236+00:00
-- url     : https://prove2.me/theorems/9819e926-24a6-4c12-8431-7a5f6be68dfa
-- title:
--   For u ∉ Q̄ with uū = ρ algebraic and a ∈ Q̄ non-zero with aā = ρ², the conjugation-stable space Q̄ + Q̄u + Q̄ū + Q̄·u/(u² − a) carries no 2×3 configuration
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ with $\rho = u\bar u$ algebraic, and let $a \in \overline{\mathbb{Q}}$, $a \neq 0$, with $a\bar a = \rho^2$. Then there are no $x_1, x_2$, independent over $\overline{\mathbb{Q}}$, and $y_1, y_2, y_3$, independent over $\overline{\mathbb{Q}}$, with all six products $x_iy_j$ in $\overline{\mathbb{Q}} + \overline{\mathbb{Q}}u + \overline{\mathbb{Q}}\bar u + \overline{\mathbb{Q}}\,u/(u^2 - a)$.
--
--   Here $z = u/(u^2 - a)$ has $\bar z = -(\rho/\bar a)z$, so the space is stable under conjugation and a hypothesis $z \in \widetilde{\mathcal{L}}$ adds nothing to it; when $a\bar a \neq \rho^2$ the five-dimensional $H_0 + \overline{\mathbb{Q}}z + \overline{\mathbb{Q}}\bar z$ does carry a configuration (`DiazModulus.circle_point_conjugate_pair_extension_carries_two_by_three_configuration`). So $\bar z$ is what lets the strong six exponentials theorem see $u/(u^2 - a)$. This is also where the hypotheses of Diaz (2004, Th. 2) and Diaz (2007, Cor. 4(4), Th. 7(1)) fail for this family: $(1, U, \bar U)$ with $U = 1/(u^2 - a)$ is $\overline{\mathbb{Q}}$-linearly dependent.
--
--   **Proof.** Put $z_2 = u/(u^2 - a)^2$. Since $\rho^2/\bar a = a$, $\bar z_2 = (\rho/\bar a^2)\,u^3/(u^2 - a)^2$, and $w = u/(u^2 - a) = (\bar a^2/\rho)\bar z_2 - a z_2$ lies in $W_2 = H_0 + \overline{\mathbb{Q}}z_2 + \overline{\mathbb{Q}}\bar z_2$. Also $w \notin H_0$: if $w = c_0 + c_1u + c_2\bar u$, multiplying by $u(u^2 - a)$ gives a polynomial $c_1X^4 + c_0X^3 + (c_2\rho - c_1a - 1)X^2 - c_0aX - c_2\rho a$ vanishing at the transcendental $u$; its coefficients in degrees $4$, $0$ and $2$ give $c_1 = 0$, $c_2 = 0$ and $-1 = 0$. So `DiazModulus.circle_point_conjugate_pair_configuration_invisible_to_four_dimensional_extensions`, for $z_2$, says that $H_0 + \overline{\mathbb{Q}}w$ carries no configuration.
--
--   **Novelty.** Not found in the sources read; a short consequence of Theorem B (`DiazModulus.circle_point_extension_two_by_three_configuration_iff`).
-- source:
--   Not found in the sources read; it marks where the hypotheses of G. Diaz, Utilisation de la conjugaison complexe dans l'étude de la transcendance de valeurs de la fonction exponentielle usuelle, J. Théor. Nombres Bordeaux 16 (2004), 535–553, Th. 2 (p. 538), and of G. Diaz, Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques : conjectures et résultats partiels, J. Théor. Nombres Bordeaux 19 (2007), 373–391, Cor. 4(4) and Th. 7(1) (pp. 383, 390), fail for this family. By DiazModulus.circle_point_extension_two_by_three_configuration_iff (Theorem B of the Diaz modulus mission). Formal proof: Diaz modulus mission, 6 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem conj_stable_circle_point_extension_no_two_by_three_configuration (u a : ℂ)
    (hu : u ∉ Qbar) (hρ : IsAlgebraic ℚ (u * conj u)) (ha : a ∈ Qbar) (ha0 : a ≠ 0)
    (haρ : a * conj a = (u * conj u) ^ 2) :
    ¬ ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
      ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, u / (u ^ 2 - a)} : Set ℂ) := by
  sorry

end DiazModulus
