-- Prove2me | Theorems.Thm_DiazModulus_two_orbit_space_visible_to_four_dimensional_extensions_iff_common_zero
-- name    : DiazModulus.two_orbit_space_visible_to_four_dimensional_extensions_iff_common_zero
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-01T09:21:09.713683+00:00
-- url     : https://prove2.me/theorems/54c322ab-5f82-4b26-9dde-6dff1c9c55e5
-- title:
--   A five-dimensional two-orbit space is visible to the four-dimensional extensions iff S₁ vanishes at a zero of P or S₂ at a zero of Q, on the projective line
-- statement:
--   Let $u \in \mathbb{C}$ be transcendental, that is, $u \notin \overline{\mathbb{Q}}$ (the algebraic numbers); spans and linear independence are over $\overline{\mathbb{Q}}$. Suppose that $\rho = u\bar u$ is algebraic. Put $H_0 = \mathrm{span}(1, u, u^{-1})$. Let $P, Q, S_1, S_2 \in \overline{\mathbb{Q}}[X]$ with $P, Q$ coprime, $\max(\deg P, \deg Q) = 2$ and $\deg S_1, \deg S_2 \leq 2$. Put $g_1 = Q(u)S_1(u)/(uP(u))$, $g_2 = P(u)S_2(u)/(uQ(u))$ and $W_A = \mathrm{span}(1, u, u^{-1}, g_1, g_2)$, the two-orbit shape (D2a) of Theorem NF. Suppose $\dim W_A = 5$. Call a $\overline{\mathbb{Q}}$-subspace $W \supseteq H_0$ of $\mathbb{C}$ visible to the four-dimensional extensions if some $w \in W \setminus H_0$ makes $\mathrm{span}(1, u, u^{-1}, w)$ carry a $2 \times 3$ configuration (linearly independent $x_0, x_1$ and linearly independent $y_0, y_1, y_2$ with all six products $x_iy_j$ in that space). Then $W_A$ is visible to the four-dimensional extensions if and only if $P$ and $S_1$ have a common zero on the projective line, or $Q$ and $S_2$ do.
--
--   Two polynomials $P, S \in \overline{\mathbb{Q}}[X]$ of degree at most $2$ have a common zero on the projective line if they are not coprime (a common root in $\overline{\mathbb{Q}}$) or their coefficients of $X^2$ are both zero (a common zero at $\infty$, reading $P$ and $S$ as binary forms of degree $2$).
--
--   In the language of the research notes, the zero sets of $P$ and $Q$ on the projective line are the two orbits, and the condition says that $S_1$, resp. $S_2$, vanishes at a point of its orbit. Visibility means that $W_A$ contains $u^2$, $u^{-2}$ or some $(u - a)^{-1}$ (`DiazModulus.visible_to_four_dimensional_extensions_iff_visible_element_mem`), a list closed under conjugation modulo $H_0$.
--
--   **Proof.** By `DiazModulus.visible_to_four_dimensional_extensions_iff_visible_element_mem`, $W_A$ is visible exactly when it contains one of $u^2$, $u^{-2}$, $(u - a)^{-1}$. “If”: $\dim W_A = 5$ gives $S_1 \notin \overline{\mathbb{Q}} P$ (otherwise $g_1 = kQ(u)/u \in H_0$ and $\dim W_A \leq 4$) and likewise $S_2 \notin \overline{\mathbb{Q}} Q$. A common zero of $P, S_1$ (resp. $Q, S_2$) puts one of these elements in $H_0 + \overline{\mathbb{Q}} g_1$ (resp. $H_0 + \overline{\mathbb{Q}} g_2$) by `DiazModulus.quadratic_fraction_extension_visible_element_mem_of_common_zero` (applied to $(P, Q, S_1)$, resp. $(Q, P, S_2)$), and these spaces lie in $W_A$. “Only if”: with no common zero on either side, `DiazModulus.invisible_two_orbit_space_u_multiplier_space_eq` gives $\{f : f, uf \in W_A\} = \mathrm{span}(1, u^{-1})$, and `DiazModulus.u_multiplier_space_le_span_no_degree_one_no_visible_element` excludes all of them.
--
--   **Novelty.** None claimed; routine. It is the visibility criterion of the project's research notes (R12), Q1.4, for two-orbit spaces, stated without roots or valuations: Theorem B (`DiazModulus.circle_point_extension_two_by_three_configuration_iff`, 10.6) through `DiazModulus.visible_to_four_dimensional_extensions_iff_visible_element_mem`, the “if” half by `DiazModulus.quadratic_fraction_extension_visible_element_mem_of_common_zero`, the “only if” half by Q1.5 (`DiazModulus.invisible_two_orbit_space_u_multiplier_space_eq`) and `DiazModulus.u_multiplier_space_le_span_no_degree_one_no_visible_element`.
-- source:
--   No novelty claimed. The visibility criterion, Q1.4 of the Diaz modulus mission's research notes (round R12), for two-orbit spaces, stated without roots or valuations; it rests on Theorem B (DiazModulus.circle_point_extension_two_by_three_configuration_iff, 10.6). Uses DiazModulus.visible_to_four_dimensional_extensions_iff_visible_element_mem, DiazModulus.quadratic_fraction_extension_visible_element_mem_of_common_zero, DiazModulus.invisible_two_orbit_space_u_multiplier_space_eq and DiazModulus.u_multiplier_space_le_span_no_degree_one_no_visible_element. R21b of the Diaz modulus mission. Formal proof: Diaz modulus mission, 30 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Polynomial in
theorem two_orbit_space_visible_to_four_dimensional_extensions_iff_common_zero (u : ℂ) (hu : u ∉ Qbar) (hρ : IsAlgebraic ℚ (u * conj u))
    (P Q S₁ S₂ : (↥Qbar)[X]) (hcop : IsCoprime P Q) (hdeg : max P.natDegree Q.natDegree = 2) (hS₁ : S₁.natDegree ≤ 2) (hS₂ : S₂.natDegree ≤ 2)
    (h5 : Module.finrank (↥Qbar) (Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P),
        aeval u P * aeval u S₂ / (u * aeval u Q)} : Set ℂ)) = 5) :
    (∃ w ∈ Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P),
        aeval u P * aeval u S₂ / (u * aeval u Q)} : Set ℂ), w ∉ Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ) ∧
        ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
          ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, u⁻¹, w} : Set ℂ)) ↔
    (¬ IsCoprime P S₁ ∨ (P.coeff 2 = 0 ∧ S₁.coeff 2 = 0)) ∨ (¬ IsCoprime Q S₂ ∨ (Q.coeff 2 = 0 ∧ S₂.coeff 2 = 0)) := by
  sorry

end DiazModulus
