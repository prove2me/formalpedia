-- Prove2me | Theorems.Thm_DiazModulus_circle_point_conjugate_pair_extension_carries_two_by_three_configuration
-- name    : DiazModulus.circle_point_conjugate_pair_extension_carries_two_by_three_configuration
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-06T07:48:03.070474+00:00
-- url     : https://prove2.me/theorems/d8abac5b-9bd4-4091-a0ed-2be61713f899
-- title:
--   For u ∉ Q̄ with uū = ρ algebraic and z = u/(u² − a) (aā ≠ ρ²) or u/(u² − a)² (aā = ρ²), a ∈ Q̄ non-zero, the space Q̄ + Q̄u + Q̄ū + Q̄z + Q̄z̄ carries a 2×3 configuration
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ with $\rho = u\bar u$ algebraic, let $a \in \overline{\mathbb{Q}}$, $a \neq 0$, and let $z$ be $u/(u^2 - a)$ if $a\bar a \neq \rho^2$, or $u/(u^2 - a)^2$ if $a\bar a = \rho^2$. Put $H_0 = \overline{\mathbb{Q}} + \overline{\mathbb{Q}}u + \overline{\mathbb{Q}}\bar u$ and $W = H_0 + \overline{\mathbb{Q}}z + \overline{\mathbb{Q}}\bar z$. Then there are $x_1, x_2$, linearly independent over $\overline{\mathbb{Q}}$, and $y_1, y_2, y_3$, linearly independent over $\overline{\mathbb{Q}}$, with all six products $x_iy_j$ in $W$.
--
--   The configuration is $x = (1, u^2)$, $y = (b, bu^2, bu^4)$, with $b = 1/(u(u^2 - a)(u^2 - a'))$ and $a' = \rho^2/\bar a$ in the first case and $b = 1/(u(u^2 - a)^2)$ in the second: $W$ contains the progression $b, bu^2, bu^4, bu^6$. Since $\widetilde{\mathcal{L}}$ is closed under complex conjugation, a hypothesis $z \in \widetilde{\mathcal{L}}$ brings $\bar z$ with it, so $W$ is the space Roy's strong six exponentials theorem sees at a candidate; `DiazModulus.circle_point_extension_two_by_three_configuration_iff` (Theorem B) treats the four-dimensional spaces $H_0 + \overline{\mathbb{Q}}w$ only. The statement does not involve $e^u$, so it keeps its content if Diaz's conjecture holds.
--
--   **Proof.** In the first case $a' = \rho^2/\bar a$ is algebraic and differs from $a$, and $\bar z = -(\rho/\bar a)\,u/(u^2 - a')$; in the second, $\rho^2/\bar a = a$ and $\bar z = (\rho/\bar a^2)\,u^3/(u^2 - a)^2$. With $u^{-1} = \bar u/\rho$, partial fractions in $v = u^2$ write each of $b, bu^2, bu^4, bu^6$ as a combination of $u$, $u^{-1}$, $z$ and $\bar z$ with algebraic coefficients; for instance $(a - a')\,bu^2 = z - u/(u^2 - a')$ in the first case and $bu^2 = z$ in the second. The six products $x_iy_j$ are $b, bu^2, bu^4, bu^2, bu^4, bu^6$. Both families are free because $u$ is transcendental over $\overline{\mathbb{Q}}$: $s + tu^2 = 0$ and, after dividing by $b \neq 0$, $g_0 + g_1u^2 + g_2u^4 = 0$ force all coefficients to vanish.
--
--   **Novelty.** Not asserted for the configuration: rescaled, it is the configuration $(u, \bar u) \times (1, U, \bar U)$, $U = 1/(u^2 - a)$, in the proofs of Diaz (2004, Th. 2) and Diaz (2007, Th. 6(1) and 7(1)), and the progression of Fischler (2001, Lemma 6.1). That no four-dimensional subspace of $W$ containing $H_0$ carries one is `DiazModulus.circle_point_conjugate_pair_configuration_invisible_to_four_dimensional_extensions`.
-- source:
--   The configuration has the shape of those in the proofs of G. Diaz, Utilisation de la conjugaison complexe dans l'étude de la transcendance de valeurs de la fonction exponentielle usuelle, J. Théor. Nombres Bordeaux 16 (2004), 535–553, Th. 2 (p. 538), and of G. Diaz, Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques : conjectures et résultats partiels, J. Théor. Nombres Bordeaux 19 (2007), 373–391, Th. 6(1) and 7(1) (pp. 389–390); rescaled, it is the progression of S. Fischler, Orbits under algebraic groups and logarithms of algebraic numbers, Acta Arith. 100 (2001), 167–187, Lemma 6.1 (p. 184). R5 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 6 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem circle_point_conjugate_pair_extension_carries_two_by_three_configuration (u a z : ℂ)
    (hu : u ∉ Qbar) (hρ : IsAlgebraic ℚ (u * conj u)) (ha : a ∈ Qbar) (ha0 : a ≠ 0)
    (hz : (a * conj a ≠ (u * conj u) ^ 2 ∧ z = u / (u ^ 2 - a)) ∨
      (a * conj a = (u * conj u) ^ 2 ∧ z = u / (u ^ 2 - a) ^ 2)) :
    ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
      ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ) := by
  sorry

end DiazModulus
