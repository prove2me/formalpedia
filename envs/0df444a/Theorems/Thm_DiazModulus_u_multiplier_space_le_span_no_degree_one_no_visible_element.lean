-- Prove2me | Theorems.Thm_DiazModulus_u_multiplier_space_le_span_no_degree_one_no_visible_element
-- name    : DiazModulus.u_multiplier_space_le_span_no_degree_one_no_visible_element
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-01T09:20:25.374208+00:00
-- url     : https://prove2.me/theorems/62c8307e-256b-44cb-856f-0fdd2b4e361b
-- title:
--   If multiplication by u keeps only span(1, 1/u) inside W, then W has no degree-one triple and contains none of u², u⁻², 1/(u − a) (a ≠ 0 algebraic)
-- statement:
--   Let $u \in \mathbb{C}$ be transcendental, that is, $u \notin \overline{\mathbb{Q}}$ (the algebraic numbers); spans and linear independence are over $\overline{\mathbb{Q}}$. Let $W \subseteq \mathbb{C}$ be a $\overline{\mathbb{Q}}$-vector subspace with $u, u^{-1} \in W$, and suppose that every $f \in W$ with $uf \in W$ lies in $\mathrm{span}(1, u^{-1})$. Then:
--
--   - (D1) fails for $W$: there are no linearly independent $t_0, t_1, t_2 \in \mathbb{C}$ with $t_j \in W$ and $ut_j \in W$ for every $j$;
--   - $W$ contains none of $u^2$, $u^{-2}$ and $(u - a)^{-1}$ for $a \in \overline{\mathbb{Q}}$, $a \neq 0$.
--
--   These are the elements of Theorem B (`DiazModulus.circle_point_extension_two_by_three_configuration_iff`) attached to the points $\infty$, $0$ and $a$ of the projective line. The hypothesis $1 \in W$ is not needed.
--
--   **Proof.** No degree-one triple: three linearly independent $t_j$ with $t_j, ut_j \in W$ would lie in the two-dimensional $\mathrm{span}(1, u^{-1})$. No $t_x$: if $u^2 \in W$ take $f = u$; if $u^{-2} \in W$ take $f = u^{-2}$, so that $uf = u^{-1}$; if $(u - a)^{-1} \in W$ with $a \in \overline{\mathbb{Q}}$, $a \neq 0$, take $f = (u - a)^{-1} - u^{-1}$, so that $uf = a(u - a)^{-1}$. In each case $f \in W$ and $uf \in W$, and $f = c + du^{-1}$ with $c, d \in \overline{\mathbb{Q}}$ clears to a polynomial relation of degree at most $2$ in $u$ with a non-zero coefficient, which transcendence forbids. The hypothesis $1 \in W$ is not used.
--
--   **Novelty.** None claimed; routine. A step of the project's proof of the visibility criterion (the project's research notes (R12), Q1.4): with Q1.5 (`DiazModulus.invisible_two_orbit_space_u_multiplier_space_eq`, `DiazModulus.invisible_cyclic_space_u_multiplier_space_eq`) it gives the “only if” halves of `DiazModulus.two_orbit_space_visible_to_four_dimensional_extensions_iff_common_zero` and `DiazModulus.cyclic_space_visible_to_four_dimensional_extensions_iff_common_zero`.
-- source:
--   No novelty claimed. A step of the proof of the visibility criterion, Q1.4 of the Diaz modulus mission's research notes (round R12); the elements u², u⁻², 1/(u − a) are those of Theorem B (DiazModulus.circle_point_extension_two_by_three_configuration_iff, 10.6). R21b of the Diaz modulus mission. Formal proof: Diaz modulus mission, 30 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem u_multiplier_space_le_span_no_degree_one_no_visible_element (u : ℂ) (hu : u ∉ Qbar) (W : Submodule (↥Qbar) ℂ)
    (hu1 : u ∈ W) (hui : u⁻¹ ∈ W)
    (hZ : ∀ f ∈ W, u * f ∈ W → f ∈ Submodule.span Qbar ({1, u⁻¹} : Set ℂ)) :
    ¬ (∃ t : Fin 3 → ℂ, LinearIndependent (↥Qbar) t ∧ ∀ j, t j ∈ W ∧ u * t j ∈ W) ∧
    ¬ (u ^ 2 ∈ W ∨ (u ^ 2)⁻¹ ∈ W ∨ ∃ a ∈ Qbar, a ≠ 0 ∧ (u - a)⁻¹ ∈ W) := by
  sorry

end DiazModulus
