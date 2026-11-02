-- Prove2me | Theorems.Thm_DiazModulus_quadratic_fraction_extension_visible_element_mem_of_common_zero
-- name    : DiazModulus.quadratic_fraction_extension_visible_element_mem_of_common_zero
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-01T09:20:17.535198+00:00
-- url     : https://prove2.me/theorems/a352aaec-92f3-4435-b044-bcfe70085eac
-- title:
--   If S and P have a common zero on the projective line, then span(1, u, 1/u, Q S/(u P)) contains u², u⁻² or some 1/(u − a)
-- statement:
--   Let $u \in \mathbb{C}$ be transcendental, that is, $u \notin \overline{\mathbb{Q}}$ (the algebraic numbers); spans and linear independence are over $\overline{\mathbb{Q}}$. Put $H_0 = \mathrm{span}(1, u, u^{-1})$. Let $P, Q, S \in \overline{\mathbb{Q}}[X]$ with $P, Q$ coprime, $\max(\deg P, \deg Q) = 2$, $\deg S \leq 2$, and $S \neq kP$ for every $k \in \overline{\mathbb{Q}}$. Suppose that $P$ and $S$ have a common zero on the projective line: they are not coprime, or their coefficients of $X^2$ are both zero. Put $g = Q(u)S(u)/(uP(u))$. Then $\mathrm{span}(1, u, u^{-1}, g)$ contains $u^2$, $u^{-2}$ or $(u - a)^{-1}$ for some non-zero $a \in \overline{\mathbb{Q}}$.
--
--   Reading $P$ and $S$ as binary forms of degree $2$, the second alternative is a common zero at $\infty$. In the terms of Theorem B (`DiazModulus.circle_point_extension_two_by_three_configuration_iff`), the four-dimensional space $H_0 + \overline{\mathbb{Q}} g$ contains one of Theorem B's elements, so it carries a $2 \times 3$ configuration when $u\bar u$ is algebraic.
--
--   **Proof.** Every case writes $g = \kappa t + h$ with $\kappa \in \overline{\mathbb{Q}}$ non-zero, $h \in H_0$ and $t$ one of $u^2$, $u^{-2}$, $(u - b)^{-1}$ with $b \in \overline{\mathbb{Q}}$ non-zero; then $t = \kappa^{-1}(g - h)$ lies in $H_0 + \overline{\mathbb{Q}} g$. The membership $h \in H_0$ always comes from $R(u)/u \in H_0$ for $\deg R \leq 2$. **Reduction.** In both cases $g = Q(u)r(u)/(um(u))$ with $m \neq 0$, $\deg m, \deg r \leq 1$, $m$ coprime to $Q$, $\deg Q = 2$ if $m$ is constant, and $r \notin \overline{\mathbb{Q}} m$. If $P$ and $S$ are not coprime, an irreducible common factor has a root $a \in \overline{\mathbb{Q}}$ (a complex root of a polynomial over $\overline{\mathbb{Q}}$ is algebraic), so $P = (X - a)m$, $S = (X - a)r$ and $u - a$ cancels; $r \in \overline{\mathbb{Q}} m$ would give $S \in \overline{\mathbb{Q}} P$. At $\infty$ take $m = P$ and $r = S$. **Core**, with $N = Qr$ of degree at most $3$. If $m = m_1$ is constant, then $\deg r = 1$, $\deg N = 3$ and $g = (\mathrm{lc}(N)/m_1)u^2 + m_1^{-1}(N - \mathrm{lc}(N)X^3)(u)/u$. If $m = m_0(X - b)$, then $Q(b) \neq 0$ by coprimality and $r(b) \neq 0$ as $r \notin \overline{\mathbb{Q}} m$, so $N(b) \neq 0$. For $b = 0$, $N - N(0) = XR$ and $g = (N(0)/m_0)u^{-2} + m_0^{-1}R(u)/u$. For $b \neq 0$, with $c = N(b)/b$, $N - cX = (X - b)R$ and $g = (c/m_0)(u - b)^{-1} + m_0^{-1}R(u)/u$.
--
--   **Novelty.** None claimed; routine. A step of the project's proof of the visibility criterion (the project's research notes (R12), Q1.4): the “if” half, written with six partial-fraction identities and no roots beyond one root in $\overline{\mathbb{Q}}$ of a linear factor.
-- source:
--   No novelty claimed. The “if” half of the visibility criterion, Q1.4 of the Diaz modulus mission's research notes (round R12), made root-free. R21b of the Diaz modulus mission. Formal proof: Diaz modulus mission, 30 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Polynomial in
theorem quadratic_fraction_extension_visible_element_mem_of_common_zero (u : ℂ) (hu : u ∉ Qbar) (P Q S : (↥Qbar)[X])
    (hcop : IsCoprime P Q) (hdeg : max P.natDegree Q.natDegree = 2) (hS : S.natDegree ≤ 2)
    (hSP : ∀ k : ↥Qbar, S ≠ C k * P) (hz : (¬ IsCoprime P S ∨ (P.coeff 2 = 0 ∧ S.coeff 2 = 0))) :
    (u ^ 2 ∈ Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S / (u * aeval u P)} : Set ℂ) ∨ (u ^ 2)⁻¹ ∈ Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S / (u * aeval u P)} : Set ℂ) ∨ ∃ a ∈ Qbar, a ≠ 0 ∧ (u - a)⁻¹ ∈ Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S / (u * aeval u P)} : Set ℂ)) := by
  sorry

end DiazModulus
