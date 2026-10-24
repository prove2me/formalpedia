-- Prove2me | Theorems.Thm_DiazModulus_conj_stable_degree_one_multiplier_space_visible_or_real_pencil_space
-- name    : DiazModulus.conj_stable_degree_one_multiplier_space_visible_or_real_pencil_space
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-23T07:19:19.430992+00:00
-- url     : https://prove2.me/theorems/bd7526f9-422a-408b-aacb-ac5532fe7917
-- title:
--   A conjugation-stable five-dimensional W ⊇ span(1, u, u⁻¹) of type D1 contains u², ū² or 1/(u − a), or is a real pencil space W(λ, f)
-- statement:
--   Let $u \in \mathbb{C}$ be transcendental, that is, $u \notin \overline{\mathbb{Q}}$ (the algebraic numbers); spans and linear independence are over $\overline{\mathbb{Q}}$. Let $s \in \overline{\mathbb{Q}}$ be real ($\bar s = s$) with $s^2 = u\bar u$. Let $W \subseteq \mathbb{C}$ be a $\overline{\mathbb{Q}}$-vector subspace of dimension $5$ with $1, u, u^{-1} \in W$, that is, $H_0 \subseteq W$ for $H_0 = \mathrm{span}(1, u, u^{-1})$. Suppose $W$ is stable under complex conjugation ($\bar w \in W$ for every $w \in W$) and satisfies (D1): there are linearly independent $t_0, t_1, t_2$ with $t_j \in W$ and $ut_j \in W$. Then one of the following holds:
--
--   - $u^2 \in W$, or $\bar u^2 \in W$, or $(u - a)^{-1} \in W$ for some $a \in \overline{\mathbb{Q}}$ with $a \neq 0$ ($W$ is visible);
--   - there are $\lambda, f \in \mathbb{C}$ with $\lambda \in \overline{\mathbb{Q}}$, $\lambda\bar\lambda = 1$, $\bar f = f$ and $W = \mathrm{span}(1, u, \bar u, f, f/(s + \lambda u))$, the real pencil space $W(\lambda, f)$.
--
--   **Proof.** As $s^2 = u\bar u \neq 0$, $\bar u = s^2u^{-1}$, so $u^{-2} \in W$ if and only if $\bar u^2 \in W$. If $W$ is visible we are done. Otherwise `DiazModulus.degree_one_multiplier_space_visible_or_degree_one_space` gives $g$ with $1, u, u^{-1}, g, ug$ independent and spanning $W$. Then $Z = \{h \in W : uh \in W\}$ is $\mathrm{span}(1, u^{-1}, g)$: for $h = a_0 + a_1u + a_2u^{-1} + a_3g + a_4ug$ in $Z$, $a_1u^2 + a_4u^2g \in W$; $a_4 = 0$ forces $a_1 = 0$ ($u^2 \notin W$); if $a_4 \neq 0$, write $u^2(g + b) = b_0 + b_1u + b_2u^{-1} + b_3g + b_4ug$ and take a root $c \in \overline{\mathbb{Q}}$ of $X^2 - b_4X - b_3$ (a square root of the discriminant is algebraic); then $F = (c - b_4)g + ug + bu \in W \setminus H_0$ has $(u - c)F \in H_0$, which puts $u^{-2}$ or $(u - c)^{-1}$ in $W$, a contradiction. Now $h = u^{-1}\bar g = s^{-2}\,\overline{ug}$ lies in $W$, and so does $uh = \bar g$; so $h \in Z$ and $\bar g \in uZ = \mathrm{span}(1, u, ug)$. Finally $1, u, \bar u, g, ug$ are independent, their span is $W$ by dimension, and `DiazModulus.conj_equivariant_degree_one_space_eq_real_pencil_space` (10.43), whose hypothesis is $\bar g \in \mathrm{span}(1, u, ug)$, gives $\lambda$ and $f$.
--
--   **Novelty.** The conjugation-stable refinement of the degree-one case, as in the project's research notes; routine; uses `DiazModulus.conj_equivariant_degree_one_space_eq_real_pencil_space` (10.43).
-- source:
--   The conjugation-stable refinement of the degree-one case in the mission's research notes; the real pencil spaces are the project's (blueprint Prop. 10.42, Thm. 10.43, DiazModulus.conj_equivariant_degree_one_space_eq_real_pencil_space). Uses DiazModulus.degree_one_multiplier_space_visible_or_degree_one_space and DiazModulus.conj_equivariant_degree_one_space_eq_real_pencil_space. R20 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 23 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem conj_stable_degree_one_multiplier_space_visible_or_real_pencil_space (u s : ℂ) (hu : u ∉ Qbar)
    (hs : s ∈ Qbar) (hsr : conj s = s) (hss : s * s = u * conj u) (W : Submodule (↥Qbar) ℂ) [FiniteDimensional (↥Qbar) W]
    (hW : Module.finrank (↥Qbar) W = 5) (h1 : (1 : ℂ) ∈ W) (hu1 : u ∈ W) (hui : u⁻¹ ∈ W)
    (hσ : ∀ w ∈ W, conj w ∈ W) (hD1 : (∃ t : Fin 3 → ℂ, LinearIndependent (↥Qbar) t ∧ ∀ j, t j ∈ W ∧ u * t j ∈ W)) :
    (u ^ 2 ∈ W ∨ conj u ^ 2 ∈ W ∨ ∃ a ∈ Qbar, a ≠ 0 ∧ (u - a)⁻¹ ∈ W) ∨
    ∃ lam f : ℂ, lam ∈ Qbar ∧ lam * conj lam = 1 ∧ conj f = f ∧
      W = Submodule.span Qbar ({1, u, conj u, f, f / (s + lam * u)} : Set ℂ) := by
  sorry

end DiazModulus
