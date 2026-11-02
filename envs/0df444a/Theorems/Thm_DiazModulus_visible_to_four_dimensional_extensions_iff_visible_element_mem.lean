-- Prove2me | Theorems.Thm_DiazModulus_visible_to_four_dimensional_extensions_iff_visible_element_mem
-- name    : DiazModulus.visible_to_four_dimensional_extensions_iff_visible_element_mem
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-01T09:20:30.008747+00:00
-- url     : https://prove2.me/theorems/bacbf9be-d82d-4c97-8793-8dffbc6648c3
-- title:
--   A space containing 1, u, 1/u is visible to the four-dimensional extensions iff it contains u², u⁻² or some 1/(u − a) with a ≠ 0
-- statement:
--   Let $u \in \mathbb{C}$ be transcendental, that is, $u \notin \overline{\mathbb{Q}}$ (the algebraic numbers); spans and linear independence are over $\overline{\mathbb{Q}}$. Suppose that $\rho = u\bar u$ is algebraic. Let $W \subseteq \mathbb{C}$ be a $\overline{\mathbb{Q}}$-vector subspace with $1, u, u^{-1} \in W$, and put $H_0 = \mathrm{span}(1, u, u^{-1})$. Call a $\overline{\mathbb{Q}}$-subspace $W \supseteq H_0$ of $\mathbb{C}$ visible to the four-dimensional extensions if some $w \in W \setminus H_0$ makes $\mathrm{span}(1, u, u^{-1}, w)$ carry a $2 \times 3$ configuration (linearly independent $x_0, x_1$ and linearly independent $y_0, y_1, y_2$ with all six products $x_iy_j$ in that space). Then $W$ is visible to the four-dimensional extensions if and only if $W$ contains $u^2$, $u^{-2}$ or $(u - a)^{-1}$ for some non-zero $a \in \overline{\mathbb{Q}}$.
--
--   As $\bar u = \rho u^{-1}$, $H_0 = \mathrm{span}(1, u, \bar u)$ and $\mathrm{span}(1, u, u^{-1}, w) = \mathrm{span}(1, u, \bar u, w)$, so this is the visibility of `DiazModulus.rational_degree_one_space_visible_to_four_dimensional_extensions_iff_natDegree_le`. Under $\rho = u\bar u \in \overline{\mathbb{Q}}$ the list $u^2$, $u^{-2}$, $(u - a)^{-1}$ is closed under complex conjugation modulo $H_0$: $\bar u^2 = \rho^2u^{-2}$, $\overline{u^{-2}} = \rho^{-2}u^2$ and $\overline{(u - a)^{-1}} = -\bar a^{-1} - (\rho/\bar a^2)(u - \rho/\bar a)^{-1}$ with $\rho/\bar a \neq 0$; so no conjugate has to be added.
--
--   **Proof.** As $\bar u = \rho u^{-1}$ with $\rho \neq 0$ algebraic, $\mathrm{span}(1, u, \bar u) = H_0$, $\mathrm{span}(1, u, \bar u, z) = \mathrm{span}(1, u, u^{-1}, z)$ for every $z$, and $\bar u^2 = \rho^2u^{-2}$. So Theorem B (`DiazModulus.circle_point_extension_two_by_three_configuration_iff`, 10.6) reads: for $z \notin H_0$, $H_0 + \overline{\mathbb{Q}} z$ carries a $2 \times 3$ configuration if and only if $z \in H_0 + \overline{\mathbb{Q}} t$ for some $t$ among $u^2$, $u^{-2}$ and the $(u - a)^{-1}$ with $a \in \overline{\mathbb{Q}}$ non-zero. “Only if”: an element $w \in W \setminus H_0$ with a configuration lies in $H_0 + \overline{\mathbb{Q}} t$; as $w \notin H_0$, the coefficient of $t$ is non-zero, and $t \in W$ by exchange. “If”: take $w = t$; each $t$ lies outside $H_0$ (clear denominators; $u$ is transcendental), and Theorem B gives the configuration.
--
--   **Novelty.** None claimed; routine. A restatement of Theorem B (`DiazModulus.circle_point_extension_two_by_three_configuration_iff`, 10.6) for spaces containing $H_0$, in the form of `DiazModulus.rational_degree_one_space_visible_to_four_dimensional_extensions_iff_natDegree_le` (10.80).
-- source:
--   No novelty claimed. Theorem B of the Diaz modulus mission (DiazModulus.circle_point_extension_two_by_three_configuration_iff, 10.6), restated for spaces containing span(1, u, 1/u) in the form of DiazModulus.rational_degree_one_space_visible_to_four_dimensional_extensions_iff_natDegree_le (10.80). Uses DiazModulus.circle_point_extension_two_by_three_configuration_iff. R21b of the Diaz modulus mission. Formal proof: Diaz modulus mission, 30 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem visible_to_four_dimensional_extensions_iff_visible_element_mem (u : ℂ) (hu : u ∉ Qbar) (hρ : IsAlgebraic ℚ (u * conj u))
    (W : Submodule (↥Qbar) ℂ) (h1 : (1 : ℂ) ∈ W) (hu1 : u ∈ W) (hui : u⁻¹ ∈ W) :
    (∃ w ∈ W, w ∉ Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ) ∧
        ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
          ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, u⁻¹, w} : Set ℂ)) ↔
    (u ^ 2 ∈ W ∨ (u ^ 2)⁻¹ ∈ W ∨ ∃ a ∈ Qbar, a ≠ 0 ∧ (u - a)⁻¹ ∈ W) := by
  sorry

end DiazModulus
