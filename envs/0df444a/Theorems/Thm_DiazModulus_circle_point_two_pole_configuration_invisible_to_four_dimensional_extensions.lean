-- Prove2me | Theorems.Thm_DiazModulus_circle_point_two_pole_configuration_invisible_to_four_dimensional_extensions
-- name    : DiazModulus.circle_point_two_pole_configuration_invisible_to_four_dimensional_extensions
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-09T09:00:54.047695+00:00
-- url     : https://prove2.me/theorems/7554ba08-b9b2-4739-8cc0-acf2e0c2ab9e
-- title:
--   For the same u, a₁, a₂, W = Q̄ + Q̄u + Q̄ū + Q̄u/(u² − a₁) + Q̄u/(u² − a₂) carries a 2×3 configuration, while no Q̄ + Q̄u + Q̄ū + Q̄w with w ∈ W outside Q̄ + Q̄u + Q̄ū does
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ with $\rho = u\bar u$ algebraic, let $a_1 \neq a_2$ be non-zero algebraic numbers, $z_i = u/(u^2 - a_i)$, $H_0 = \overline{\mathbb{Q}} + \overline{\mathbb{Q}}u + \overline{\mathbb{Q}}\bar u$ and $W = H_0 + \overline{\mathbb{Q}}z_1 + \overline{\mathbb{Q}}z_2$. Then $W$ carries a $2 \times 3$ configuration, but for no $w \in W$ outside $H_0$ does $H_0 + \overline{\mathbb{Q}}w$ carry one.
--
--   This removes the conjugation condition from `DiazModulus.circle_point_conjugate_pair_configuration_invisible_to_four_dimensional_extensions` (the case $a_2 = \rho^2/\bar a_1$), and covers the case $a_1\bar a_1 = a_2\bar a_2 = \rho^2$, where $W$ is stable under conjugation.
--
--   **Proof.** The configuration is `DiazModulus.circle_point_two_pole_extension_carries_two_by_three_configuration`. If $w \in W \setminus H_0$ and $H_0 + \overline{\mathbb{Q}}w$ carried one, Theorem B (`DiazModulus.circle_point_extension_two_by_three_configuration_iff`) would give $w \in H_0 + \overline{\mathbb{Q}}t$ with $t$ one of $u^2$, $\bar u^2$, $1/(u - b)$ ($b$ algebraic, non-zero); exchange then puts $t$ in $H_0 + \overline{\mathbb{Q}}w \subseteq W$, which `DiazModulus.circle_point_two_pole_extension_excludes_squares_and_reciprocals` rules out.
--
--   **Novelty.** Not found in the sources read; it is short (parity plus Theorem B).
-- source:
--   Not found in the sources read; the configuration's shape is printed (S. Fischler, Orbits under algebraic groups and logarithms of algebraic numbers, Acta Arith. 100 (2001), 167–187, Lemma 6.1). Uses DiazModulus.circle_point_extension_two_by_three_configuration_iff (Theorem B of the Diaz modulus mission). R7 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 9 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem circle_point_two_pole_configuration_invisible_to_four_dimensional_extensions (u a₁ a₂ : ℂ)
    (hu : u ∉ Qbar) (hρ : IsAlgebraic ℚ (u * conj u)) (ha₁ : a₁ ∈ Qbar) (ha₂ : a₂ ∈ Qbar)
    (ha₁0 : a₁ ≠ 0) (ha₂0 : a₂ ≠ 0) (ha : a₁ ≠ a₂) :
    (∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
      ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, u / (u ^ 2 - a₁), u / (u ^ 2 - a₂)} : Set ℂ)) ∧
      ∀ w ∈ Submodule.span Qbar ({1, u, conj u, u / (u ^ 2 - a₁), u / (u ^ 2 - a₂)} : Set ℂ),
        w ∉ Submodule.span Qbar ({1, u, conj u} : Set ℂ) →
        ¬ ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧
          LinearIndependent (↥Qbar) y ∧
          ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, w} : Set ℂ) := by
  sorry

end DiazModulus
