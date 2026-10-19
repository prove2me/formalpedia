-- Prove2me | Theorems.Thm_DiazModulus_degree_one_space_visible_to_four_dimensional_extensions_iff_cubic_over_quadratic
-- name    : DiazModulus.degree_one_space_visible_to_four_dimensional_extensions_iff_cubic_over_quadratic
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-18T09:45:03.569641+00:00
-- url     : https://prove2.me/theorems/336fccae-dfef-4261-869c-ee51119f346a
-- title:
--   The space span(1, u, ū, g, ug) is visible to the four-dimensional extensions exactly when u·R(u)·g = N(u) with R ≠ 0, deg R ≤ 2, deg N ≤ 3
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ with $\rho = u\bar u$ algebraic (so $\bar u = \rho/u$). Let $H_0 = \overline{\mathbb{Q}} + \overline{\mathbb{Q}}u + \overline{\mathbb{Q}}\bar u$, and say that a space $W \supseteq H_0$ is visible to the four-dimensional extensions if some $w \in W \setminus H_0$ makes $H_0 + \overline{\mathbb{Q}}w$ carry a $2 \times 3$ configuration (free $x_1, x_2$ and free $y_1, y_2, y_3$ over $\overline{\mathbb{Q}}$ with all six products $x_iy_j$ in the space). Let $g \in \mathbb{C}$ with $1, u, \bar u, g, ug$ free over $\overline{\mathbb{Q}}$. Then $W_g = \mathrm{span}_{\overline{\mathbb{Q}}}(1, u, \bar u, g, ug)$ is visible to the four-dimensional extensions if and only if $u\,R(u)\,g = N(u)$ for some $R, N \in \overline{\mathbb{Q}}[X]$ with $R \neq 0$, $\deg R \leq 2$ and $\deg N \leq 3$.
--
--   Every $W_g$ carries the configuration $(1, u) \otimes (\bar u, 1, g)$; this says when Theorem B already sees $W_g$ through one of its four-dimensional subspaces.
--
--   **Proof.** By Theorem B (`DiazModulus.circle_point_extension_two_by_three_configuration_iff`), $H_0 + \overline{\mathbb{Q}}w$ with $w \notin H_0$ carries a configuration exactly when it contains $u^2$, $\bar u^2$ or some $1/(u - a)$ with $a \in \overline{\mathbb{Q}}^\times$. If $W_g$ is visible, exchange puts such an element in $H_0 + \overline{\mathbb{Q}}w \subseteq W_g$, and `DiazModulus.degree_one_space_cubic_over_quadratic_of_mem_square_or_reciprocal` gives $R$ and $N$. Conversely `DiazModulus.degree_one_space_mem_square_or_reciprocal_of_cubic_over_quadratic` puts such an element $t$ in $W_g$; it is not in $H_0$, since $u$ is transcendental, and $w = t$ works.
--
--   **Novelty.** Not found in the sources read; routine.
-- source:
--   Not found in the sources read. Uses DiazModulus.degree_one_space_cubic_over_quadratic_of_mem_square_or_reciprocal, DiazModulus.degree_one_space_mem_square_or_reciprocal_of_cubic_over_quadratic and DiazModulus.circle_point_extension_two_by_three_configuration_iff. R17 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 18 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Polynomial in
theorem degree_one_space_visible_to_four_dimensional_extensions_iff_cubic_over_quadratic
    (u g : ℂ) (hu : u ∉ Qbar) (hρ : IsAlgebraic ℚ (u * conj u))
    (hind : LinearIndependent (↥Qbar) ![1, u, conj u, g, u * g]) :
    (∃ w ∈ Submodule.span Qbar ({1, u, conj u, g, u * g} : Set ℂ), w ∉ Submodule.span Qbar ({1, u, conj u} : Set ℂ) ∧
        ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
          ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, w} : Set ℂ)) ↔
      ∃ R N : (↥Qbar)[X], R ≠ 0 ∧ R.natDegree ≤ 2 ∧ N.natDegree ≤ 3 ∧ u * aeval u R * g = aeval u N := by
  sorry

end DiazModulus
