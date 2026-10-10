-- Prove2me | Theorems.Thm_ContinuityEqWiki_integral_div_eq_boxFlux
-- name    : ContinuityEqWiki.integral_div_eq_boxFlux
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:27:00.32499+00:00
-- url     : https://prove2.me/theorems/37b051ed-205e-4548-a86d-745f639ad4f2
-- title:
--   Divergence theorem on a box: $\int_V\nabla\cdot F=\oint_{\partial V}F\cdot d\mathbf S$
-- statement:
--   Let $V=[a,b]=\prod_{i=0}^{2}[a_i,b_i]\subset\mathbb R^3$ be a closed box with $a\le b$ coordinatewise, and let $F:\mathbb R^3\to\mathbb R^3$ be a continuously differentiable vector field. Then
--   $$\int_V \nabla\cdot F(x)\,dx=\oint_{\partial V}F\cdot d\mathbf S,$$
--   where the right-hand side is the outward flux of $F$ through the six faces of $V$.
--
--   This is the divergence theorem invoked by the source to pass from the integral form of the continuity equation to its differential form.
--
--   **Formalization Note** The closed surface is the boundary of an axis-parallel box, as in Mathlib's divergence theorem; the flux is the sum over $i$ of the face integrals of $F_i$ over $x_i=b_i$ minus those over $x_i=a_i$.
-- source:
--   Wikipedia, "Continuity equation", revision oldid=1378634825, https://en.wikipedia.org/w/index.php?title=Continuity_equation&oldid=1378634825, section "Differential form" ("By the divergence theorem, a general continuity equation can also be written in a differential form")

import Mathlib
import Definitions.Def_ContinuityEqWiki_Defs

namespace ContinuityEqWiki

theorem integral_div_eq_boxFlux (F : Space → Space) (hF : ContDiff ℝ 1 F)
    (a b : Space) (hab : a ≤ b) :
    ∫ x in Set.Icc a b, div F x = boxFlux F a b := by sorry

end ContinuityEqWiki
