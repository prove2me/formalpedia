-- Prove2me | Theorems.Thm_DiazModulus_cyclic_space_visible_to_four_dimensional_extensions_iff_common_zero
-- name    : DiazModulus.cyclic_space_visible_to_four_dimensional_extensions_iff_common_zero
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-01T09:19:54.4502+00:00
-- url     : https://prove2.me/theorems/1950d52a-edb0-45bb-908f-2a1e6a9b9f32
-- title:
--   A five-dimensional cyclic space is visible to the four-dimensional extensions iff S₁ vanishes at a zero of P on the projective line
-- statement:
--   Let $u \in \mathbb{C}$ be transcendental, that is, $u \notin \overline{\mathbb{Q}}$ (the algebraic numbers); spans and linear independence are over $\overline{\mathbb{Q}}$. Suppose that $\rho = u\bar u$ is algebraic. Put $H_0 = \mathrm{span}(1, u, u^{-1})$. Let $P, Q, S_1, S_2 \in \overline{\mathbb{Q}}[X]$ with $P, Q$ coprime, $\max(\deg P, \deg Q) = 2$ and $\deg S_1, \deg S_2 \leq 2$. Put $g_1 = Q(u)S_1(u)/(uP(u))$, $g_2 = Q(u)(Q(u)S_1(u) + P(u)S_2(u))/(uP(u)^2)$ and $W_B = \mathrm{span}(1, u, u^{-1}, g_1, g_2)$, the cyclic shape (D2b) of Theorem NF. Suppose $\dim W_B = 5$. Call a $\overline{\mathbb{Q}}$-subspace $W \supseteq H_0$ of $\mathbb{C}$ visible to the four-dimensional extensions if some $w \in W \setminus H_0$ makes $\mathrm{span}(1, u, u^{-1}, w)$ carry a $2 \times 3$ configuration (linearly independent $x_0, x_1$ and linearly independent $y_0, y_1, y_2$ with all six products $x_iy_j$ in that space). Then $W_B$ is visible to the four-dimensional extensions if and only if $P$ and $S_1$ have a common zero on the projective line.
--
--   Two polynomials $P, S \in \overline{\mathbb{Q}}[X]$ of degree at most $2$ have a common zero on the projective line if they are not coprime (a common root in $\overline{\mathbb{Q}}$) or their coefficients of $X^2$ are both zero (a common zero at $\infty$, reading $P$ and $S$ as binary forms of degree $2$).
--
--   In the language of the research notes, the zero set of $P$ on the projective line is the orbit, and the condition says that $S_1$ vanishes at a point of it. Visibility means that $W_B$ contains $u^2$, $u^{-2}$ or some $(u - a)^{-1}$ (`DiazModulus.visible_to_four_dimensional_extensions_iff_visible_element_mem`), a list closed under conjugation modulo $H_0$.
--
--   **Proof.** By `DiazModulus.visible_to_four_dimensional_extensions_iff_visible_element_mem`, $W_B$ is visible exactly when it contains one of $u^2$, $u^{-2}$, $(u - a)^{-1}$. “If”: $\dim W_B = 5$ gives $S_1 \notin \overline{\mathbb{Q}} P$ (otherwise $g_1 = kQ(u)/u \in H_0$ and $\dim W_B \leq 4$), and a common zero of $P, S_1$ puts one of these elements in $H_0 + \overline{\mathbb{Q}} g_1 \subseteq W_B$ by `DiazModulus.quadratic_fraction_extension_visible_element_mem_of_common_zero`. “Only if”: with no common zero, `DiazModulus.invisible_cyclic_space_u_multiplier_space_eq` gives $\{f : f, uf \in W_B\} = \mathrm{span}(1, u^{-1})$, and `DiazModulus.u_multiplier_space_le_span_no_degree_one_no_visible_element` excludes all of them.
--
--   **Novelty.** None claimed; routine. It is the visibility criterion of the project's research notes (R12), Q1.4, for cyclic spaces, stated without roots or valuations: Theorem B (`DiazModulus.circle_point_extension_two_by_three_configuration_iff`, 10.6) through `DiazModulus.visible_to_four_dimensional_extensions_iff_visible_element_mem`, the “if” half by `DiazModulus.quadratic_fraction_extension_visible_element_mem_of_common_zero`, the “only if” half by Q1.5 (`DiazModulus.invisible_cyclic_space_u_multiplier_space_eq`) and `DiazModulus.u_multiplier_space_le_span_no_degree_one_no_visible_element`.
-- source:
--   No novelty claimed. The visibility criterion, Q1.4 of the Diaz modulus mission's research notes (round R12), for cyclic spaces, stated without roots or valuations; it rests on Theorem B (DiazModulus.circle_point_extension_two_by_three_configuration_iff, 10.6). Uses DiazModulus.visible_to_four_dimensional_extensions_iff_visible_element_mem, DiazModulus.quadratic_fraction_extension_visible_element_mem_of_common_zero, DiazModulus.invisible_cyclic_space_u_multiplier_space_eq and DiazModulus.u_multiplier_space_le_span_no_degree_one_no_visible_element. R21b of the Diaz modulus mission. Formal proof: Diaz modulus mission, 30 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Polynomial in
theorem cyclic_space_visible_to_four_dimensional_extensions_iff_common_zero (u : ℂ) (hu : u ∉ Qbar) (hρ : IsAlgebraic ℚ (u * conj u))
    (P Q S₁ S₂ : (↥Qbar)[X]) (hcop : IsCoprime P Q) (hdeg : max P.natDegree Q.natDegree = 2) (hS₁ : S₁.natDegree ≤ 2) (hS₂ : S₂.natDegree ≤ 2)
    (h5 : Module.finrank (↥Qbar) (Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P),
        aeval u Q * (aeval u Q * aeval u S₁ + aeval u P * aeval u S₂) / (u * aeval u P ^ 2)} : Set ℂ)) = 5) :
    (∃ w ∈ Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P),
        aeval u Q * (aeval u Q * aeval u S₁ + aeval u P * aeval u S₂) / (u * aeval u P ^ 2)} : Set ℂ), w ∉ Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ) ∧
        ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
          ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, u⁻¹, w} : Set ℂ)) ↔
    (¬ IsCoprime P S₁ ∨ (P.coeff 2 = 0 ∧ S₁.coeff 2 = 0)) := by
  sorry

end DiazModulus
