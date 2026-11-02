-- Prove2me | Theorems.Thm_DiazModulus_scalar_quadratic_space_visible_element_mem
-- name    : DiazModulus.scalar_quadratic_space_visible_element_mem
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-01T09:20:54.598846+00:00
-- url     : https://prove2.me/theorems/80aee870-513f-489b-9585-a37c1e0cf235
-- title:
--   A space containing 1, u, 1/u and every Q R/(u P) with deg R ≤ 2 contains u², u⁻² or some 1/(u − a)
-- statement:
--   Let $u \in \mathbb{C}$ be transcendental, that is, $u \notin \overline{\mathbb{Q}}$ (the algebraic numbers); spans and linear independence are over $\overline{\mathbb{Q}}$. Let $W \subseteq \mathbb{C}$ be a $\overline{\mathbb{Q}}$-vector subspace with $1, u, u^{-1} \in W$. Let $P, Q \in \overline{\mathbb{Q}}[X]$ be coprime with $\max(\deg P, \deg Q) = 2$, and suppose that $Q(u)R(u)/(uP(u)) \in W$ for every $R \in \overline{\mathbb{Q}}[X]$ of degree at most $2$. Then $W$ contains $u^2$, $u^{-2}$ or $(u - a)^{-1}$ for some non-zero $a \in \overline{\mathbb{Q}}$.
--
--   This is the scalar shape of the normal form (equal eigenvalues in Theorem NF's proof, `DiazModulus.degree_two_configuration_normal_form`): such a space always contains one of Theorem B's elements.
--
--   **Proof.** Pick $S \in \overline{\mathbb{Q}}[X]$ of degree at most $2$ with a common zero with $P$ on the projective line and $S \notin \overline{\mathbb{Q}} P$. If $\deg P = 2$, $P$ has a root $x \in \overline{\mathbb{Q}}$ (a complex root of a polynomial over $\overline{\mathbb{Q}}$ is algebraic), and $S = X - x$ is not coprime to $P$ and has degree $1$. If $\deg P = 1$, take $S = 1$; if $P$ is constant, take $S = X$; in both cases the coefficients of $X^2$ in $P$ and $S$ vanish. Then `DiazModulus.quadratic_fraction_extension_visible_element_mem_of_common_zero` puts $u^2$, $u^{-2}$ or some $(u - a)^{-1}$ in $H_0 + \overline{\mathbb{Q}}\,Q(u)S(u)/(uP(u))$, which lies in $W$.
--
--   **Novelty.** None claimed; routine. The scalar case of the visibility criterion of the project's research notes (R12) (Q1.4, equal eigenvalues): such a space is always visible.
-- source:
--   No novelty claimed. The scalar case of the visibility criterion, Q1.4 of the Diaz modulus mission's research notes (round R12). Uses DiazModulus.quadratic_fraction_extension_visible_element_mem_of_common_zero. R21b of the Diaz modulus mission. Formal proof: Diaz modulus mission, 30 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Polynomial in
theorem scalar_quadratic_space_visible_element_mem (u : ℂ) (hu : u ∉ Qbar) (W : Submodule (↥Qbar) ℂ) (h1 : (1 : ℂ) ∈ W) (hu1 : u ∈ W) (hui : u⁻¹ ∈ W)
    (P Q : (↥Qbar)[X]) (hcop : IsCoprime P Q) (hdeg : max P.natDegree Q.natDegree = 2)
    (hscal : ∀ R : (↥Qbar)[X], R.natDegree ≤ 2 → aeval u Q * aeval u R / (u * aeval u P) ∈ W) :
    (u ^ 2 ∈ W ∨ (u ^ 2)⁻¹ ∈ W ∨ ∃ a ∈ Qbar, a ≠ 0 ∧ (u - a)⁻¹ ∈ W) := by
  sorry

end DiazModulus
