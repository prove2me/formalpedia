-- Prove2me | Theorems.Thm_DiazModulus_two_by_two_config_critical_progression
-- name    : DiazModulus.two_by_two_config_critical_progression
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-08T13:10:13.119198+00:00
-- url     : https://prove2.me/theorems/f27b3462-2ab3-4f63-9294-ba165ea51ef5
-- title:
--   If K-independent x₁, x₂ and y₁, y₂ have products spanning a 3-dimensional K-space, then span(x) = K·a + K·ah and span(y) = K·b + K·bh for one h ∉ K
-- statement:
--   Let $K$ be a subfield of $\mathbb{C}$, and let $x_1, x_2$ and $y_1, y_2$ be complex numbers, each pair linearly independent over $K$, such that the four products $x_iy_j$ span a $K$-space of dimension $3$. Then there are $h \notin K$ and non-zero $a, b$ with $\operatorname{span}_K(x_1, x_2) = Ka + Kah$ and $\operatorname{span}_K(y_1, y_2) = Kb + Kbh$; the products span the three-term progression $ab\,(K + Kh + Kh^2)$.
--
--   The certificate $(1, u) \otimes (1, \bar u)$ of a point of a circle is of this kind, with $h = u$.
--
--   **Proof.** Four vectors in a space of dimension $3$ are dependent, so $x_1u' + x_2v = 0$ with $u' = g_{11}y_1 + g_{12}y_2$, $v = g_{21}y_1 + g_{22}y_2$ and $g \neq 0$; then $v \neq 0$. Put $h = x_2/x_1 \notin K$, $a = x_1$, $b = v$; then $bh = -u'$, the pair $v, -u'$ is independent (a relation $sv - tu' = 0$ gives $v(sx_1 + tx_2) = 0$), and it spans the same $2$-dimensional space as $y_1, y_2$.
--
--   **Novelty.** Known in general: the dimension-2 case of Bachoc, Serra and Zémor (2017), Lemmas 4–5 (there for $K$ algebraically closed in the ambient field), and of their linear Vosper theorem (Th. 33) over algebraically closed fields. Here over any subfield of $\mathbb{C}$. Not claimed.
-- source:
--   The dimension-2 case of C. Bachoc, O. Serra, G. Zémor, An analogue of Vosper's theorem for extension fields, Math. Proc. Cambridge Philos. Soc. (2017), arXiv:1501.00602, Lemmas 4–5 (stated there for a base field algebraically closed in the extension). R6 of the Diaz modulus mission (the polar-degree note). Formal proof: Diaz modulus mission, 8 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem two_by_two_config_critical_progression (K : Subfield ℂ) (x y : Fin 2 → ℂ)
    (hx : LinearIndependent K x) (hy : LinearIndependent K y)
    (h3 : Module.finrank K
      (Submodule.span K (Set.range fun ij : Fin 2 × Fin 2 => x ij.1 * y ij.2)) = 3) :
    ∃ h a b : ℂ, h ∉ K ∧ a ≠ 0 ∧ b ≠ 0 ∧
      Submodule.span K (Set.range x) = Submodule.span K {a, a * h} ∧
      Submodule.span K (Set.range y) = Submodule.span K {b, b * h} := by
  sorry

end DiazModulus
