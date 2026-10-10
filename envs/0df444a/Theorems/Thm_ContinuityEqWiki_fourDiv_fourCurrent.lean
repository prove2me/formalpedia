-- Prove2me | Theorems.Thm_ContinuityEqWiki_fourDiv_fourCurrent
-- name    : ContinuityEqWiki.fourDiv_fourCurrent
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:31:56.118685+00:00
-- url     : https://prove2.me/theorems/ec73a9db-0036-4d5b-8c05-ed1ccec7b48a
-- title:
--   Four-divergence of the four-current: $\partial_\mu J^\mu=c\,\frac{\partial\rho}{\partial(ct)}+\nabla\cdot\mathbf j$
-- statement:
--   Let $c>0$ be the speed of light, and let $\rho:\mathbb R\times\mathbb R^3\to\mathbb R$ and $\mathbf j:\mathbb R\times\mathbb R^3\to\mathbb R^3$ be a density and its current, both $C^1$ jointly in $(t,x)$. Form the four-current $J=(c\rho,j_x,j_y,j_z)$ as a field on spacetime with coordinates $(x^0,x)$, $x^0=ct$. Then at every spacetime point $(ct,x)$,
--   $$\partial_\mu J^\mu=c\frac{\partial\rho}{\partial(ct)}+\nabla\cdot\mathbf j=\frac{\partial\rho}{\partial t}+\nabla\cdot\mathbf j .$$
--
--   This identifies the four-divergence of the four-current with the left-hand side of the continuity equation.
-- source:
--   Wikipedia, "Continuity equation", revision oldid=1378634825, https://en.wikipedia.org/w/index.php?title=Continuity_equation&oldid=1378634825, section "Relativistic version", subsection "Special relativity" (4-current and its 4-divergence)

import Mathlib
import Definitions.Def_ContinuityEqWiki_Defs

namespace ContinuityEqWiki

theorem fourDiv_fourCurrent (c : ℝ) (hc : 0 < c) (ρ : ℝ → Space → ℝ) (j : ℝ → Space → Space)
    (hρ : ContDiff ℝ 1 (Function.uncurry ρ)) (hj : ContDiff ℝ 1 (Function.uncurry j))
    (t : ℝ) (x : Space) :
    fourDiv (fourCurrent c ρ j) (spacetimePoint c t x) = timeDeriv ρ t x + div (j t) x := by sorry

end ContinuityEqWiki
