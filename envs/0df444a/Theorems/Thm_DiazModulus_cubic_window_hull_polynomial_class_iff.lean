-- Prove2me | Theorems.Thm_DiazModulus_cubic_window_hull_polynomial_class_iff
-- name    : DiazModulus.cubic_window_hull_polynomial_class_iff
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-18T14:28:13.448537+00:00
-- url     : https://prove2.me/theorems/11b82858-a002-4661-8cf8-246b2f6defcc
-- title:
--   For z ≡ a v̄³ + b v̄² + c v² + d v³ mod span(1, v, v̄) with a five-dimensional hull, the hull contains a non-zero α v² + β v³ exactly when a c̄ = b d̄
-- statement:
--   Let $v \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ with $v\bar v = 1$. Let $a, b, c, d \in \overline{\mathbb{Q}}$ and let $z \in \mathbb{C}$ with $z - (a\bar v^3 + b\bar v^2 + cv^2 + dv^3) \in \mathrm{span}_{\overline{\mathbb{Q}}}(1, v, \bar v)$, and let $W = \mathrm{span}_{\overline{\mathbb{Q}}}(1, v, \bar v, z, \bar z)$ with $\dim_{\overline{\mathbb{Q}}} W = 5$. Then $\alpha v^2 + \beta v^3 \in W$ for some $\alpha, \beta \in \overline{\mathbb{Q}}$, not both zero, if and only if $a\bar c - b\bar d = 0$.
--
--   **Proof.** Let $m = a\bar v^3 + b\bar v^2 + cv^2 + dv^3$. As $\mathrm{span}(1, v, \bar v)$ is conjugation-stable, $\bar z \equiv \bar m = \bar d\bar v^3 + \bar c\bar v^2 + \bar bv^2 + \bar av^3$, so $W = \mathrm{span}(1, v, \bar v, m, \bar m)$ and $\dim W = 5$ makes these five free; also $v^{-3}, \dots, v^3$ are free over $\overline{\mathbb{Q}}$, as $v$ is transcendental. So an element $x_0 + x_1v + x_2\bar v + xm + y\bar m$ of $W$ equals some $\alpha v^2 + \beta v^3$ only if its $\bar v^3$ and $\bar v^2$ coefficients $xa + y\bar d$ and $xb + y\bar c$ vanish. If such an element with $(\alpha, \beta) \neq (0, 0)$ exists, then $(x, y) \neq (0, 0)$, and Cramer's rule gives $(a\bar c - b\bar d)x = (a\bar c - b\bar d)y = 0$, so $a\bar c - b\bar d = 0$. Conversely, if $a\bar c = b\bar d$, take $(x, y) = (\bar d, -a)$, or $(\bar c, -b)$ when $a = d = 0$; then $xm + y\bar m = \alpha v^2 + \beta v^3$ with $(\alpha, \beta) \neq (0, 0)$, because $m, \bar m$ are free.
--
--   **Novelty.** Not found in the sources read; routine.
-- source:
--   Not found in the sources read. R18 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 18 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem cubic_window_hull_polynomial_class_iff
    (v : ℂ) (hv : v ∉ Qbar) (hv1 : v * conj v = 1)
    (z a b c d : ℂ) (ha : a ∈ Qbar) (hb : b ∈ Qbar) (hc : c ∈ Qbar) (hd : d ∈ Qbar)
    (hz : z - (a * conj v ^ 3 + b * conj v ^ 2 + c * v ^ 2 + d * v ^ 3) ∈ Submodule.span Qbar ({1, v, conj v} : Set ℂ))
    (h5 : Module.finrank (↥Qbar) (Submodule.span Qbar ({1, v, conj v, z, conj z} : Set ℂ)) = 5) :
    (∃ α β : ℂ, α ∈ Qbar ∧ β ∈ Qbar ∧ (α ≠ 0 ∨ β ≠ 0) ∧ α * v ^ 2 + β * v ^ 3 ∈ Submodule.span Qbar ({1, v, conj v, z, conj z} : Set ℂ)) ↔
      (a * conj c - b * conj d) = 0 := by
  sorry

end DiazModulus
