-- Prove2me | Theorems.Thm_DiazModulus_circle_hull_progression_contains_square_or_reciprocal
-- name    : DiazModulus.circle_hull_progression_contains_square_or_reciprocal
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-05T07:47:10.478391+00:00
-- url     : https://prove2.me/theorems/1706d5e7-e333-42e4-8cad-2b8657fafca8
-- title:
--   A geometric progression b, bh, bh², bh³ (h ∉ Q̄) whose span contains 1, u and ū, for u ∉ Q̄ with uū algebraic, also contains u², ū² or 1/(u − a) for some non-zero algebraic a
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ with $u\bar u$ algebraic, let $b \neq 0$ and $h \notin \overline{\mathbb{Q}}$, and put $V = \overline{\mathbb{Q}}\,b + \overline{\mathbb{Q}}\,bh + \overline{\mathbb{Q}}\,bh^2 + \overline{\mathbb{Q}}\,bh^3$. If $1$, $u$ and $\bar u$ lie in $V$, then $V$ contains $u^2$, or $\bar u^2$, or $1/(u - a)$ for some $a \in \overline{\mathbb{Q}}$, $a \neq 0$.
--
--   It is the step of `DiazModulus.circle_point_extension_two_by_three_configuration_iff` that follows `DiazModulus.two_by_three_configuration_forces_progression`: a configuration in $\overline{\mathbb{Q}} + \overline{\mathbb{Q}}u + \overline{\mathbb{Q}}\bar u + \overline{\mathbb{Q}}z$ makes that space such a progression, and the element found here then pins down $z$.
--
--   **Proof.** Every element of $V$ is $b\,P(h)$ with $\deg P \le 3$. Write $1 = bP_0(h)$, $u = bP_1(h)$ and $u^{-1} = \bar u/(u\bar u) = bP_2(h)$. Since $h$ is transcendental, $P_1P_2 = P_0^2$, and $P_0, P_1$ are independent because $u \notin \overline{\mathbb{Q}}$. By `DiazModulus.cubic_product_eq_square_normal_form`, $P_0 = gQ_0Q_1$, $P_1 = gQ_1^2$ and $P_2 = gQ_0^2$ with $g = aQ_0 + cQ_1$, so $u\,Q_0(h) = Q_1(h)$. If $c = 0$, then $u^2 = b\,aQ_1(h)^3$; if $a = 0$, then $\bar u^2 = b\,\rho^2c\,Q_0(h)^3$ with $\rho = u\bar u$; otherwise $1/(u + a/c) = b\,c\,Q_0(h)^2Q_1(h)$. Each right-hand side is $b$ times a polynomial of degree at most $3$ in $h$, so it lies in $V$.
--
--   **Novelty.** Not asserted separately; it is a step of Theorem B.
-- source:
--   A step of DiazModulus.circle_point_extension_two_by_three_configuration_iff (Theorem B of the Diaz modulus mission), whose classification was not found in the sources read. Formal proof: Diaz modulus mission, 5 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem circle_hull_progression_contains_square_or_reciprocal (u b h : ℂ) (V : Submodule (↥Qbar) ℂ)
    (hu : u ∉ Qbar) (hρ : IsAlgebraic ℚ (u * conj u)) (hb : b ≠ 0) (hh : h ∉ Qbar)
    (hV : V = Submodule.span (↥Qbar) (Set.range fun k : Fin 4 => b * h ^ (k : ℕ)))
    (h1 : (1 : ℂ) ∈ V) (hu' : u ∈ V) (hū : conj u ∈ V) :
    u ^ 2 ∈ V ∨ conj u ^ 2 ∈ V ∨ ∃ a ∈ Qbar, a ≠ 0 ∧ (u - a)⁻¹ ∈ V := by
  sorry

end DiazModulus
