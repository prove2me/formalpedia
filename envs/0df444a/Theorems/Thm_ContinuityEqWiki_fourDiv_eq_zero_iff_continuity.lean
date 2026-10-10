-- Prove2me | Theorems.Thm_ContinuityEqWiki_fourDiv_eq_zero_iff_continuity
-- name    : ContinuityEqWiki.fourDiv_eq_zero_iff_continuity
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:32:34.672042+00:00
-- url     : https://prove2.me/theorems/7aa2da4e-9f3d-43d7-9592-8f28d9c7c1dc
-- title:
--   Relativistic continuity equation: $\partial_\mu J^\mu=0\iff\partial_t\rho+\nabla\cdot\mathbf j=0$
-- statement:
--   Let $c>0$, and let $\rho:\mathbb R\times\mathbb R^3\to\mathbb R$ and $\mathbf j:\mathbb R\times\mathbb R^3\to\mathbb R^3$ be $C^1$ jointly in $(t,x)$, with four-current $J=(c\rho,j_x,j_y,j_z)$. Then
--   $$\partial_\mu J^\mu=0\ \text{ on all of spacetime}\quad\Longleftrightarrow\quad \frac{\partial\rho}{\partial t}+\nabla\cdot\mathbf j=0\ \text{ for all } t,x .$$
--
--   This is the manifestly covariant form of the source-free continuity equation.
-- source:
--   Wikipedia, "Continuity equation", revision oldid=1378634825, https://en.wikipedia.org/w/index.php?title=Continuity_equation&oldid=1378634825, section "Relativistic version", subsection "Special relativity" ("Then the continuity equation is $\partial_\mu J^\mu=0$")

import Mathlib
import Definitions.Def_ContinuityEqWiki_Defs

namespace ContinuityEqWiki

theorem fourDiv_eq_zero_iff_continuity (c : ℝ) (hc : 0 < c) (ρ : ℝ → Space → ℝ)
    (j : ℝ → Space → Space)
    (hρ : ContDiff ℝ 1 (Function.uncurry ρ)) (hj : ContDiff ℝ 1 (Function.uncurry j)) :
    (∀ X : Spacetime, fourDiv (fourCurrent c ρ j) X = 0) ↔
      ∀ (t : ℝ) (x : Space), timeDeriv ρ t x + div (j t) x = 0 := by sorry

end ContinuityEqWiki
