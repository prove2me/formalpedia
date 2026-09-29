-- Prove2me | Theorems.Thm_ClayNavierStokes_existence_and_smoothness_periodic
-- name    : ClayNavierStokes.existence_and_smoothness_periodic
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T18:40:39.460235+00:00
-- url     : https://prove2.me/theorems/bacd3114-9310-4b75-a272-42ec574b7232
-- title:
--   (B) Existence and smoothness of Navier–Stokes solutions on $\mathbb R^3/\mathbb Z^3$
-- statement:
--   Let $\nu>0$ and let $u_0:\mathbb R^3\to\mathbb R^3$ be smooth, divergence-free and $1$-periodic in each coordinate. Then there exist smooth $u,p$ on $\mathbb R^3\times[0,\infty)$, both $1$-periodic in space, with
--   $$\partial_t u+(u\cdot\nabla)u=\nu\Delta u-\nabla p,\qquad \operatorname{div}u=0,\qquad u(x,0)=u_0(x).$$
--
--   This is alternative (B) of the Clay problem (pressure periodicity per the errata); it implies the mission goal.
--
--   **Formalization Note** Time derivatives are one-sided at $t=0$ (taken within $[0,\infty)$, resp. $[0,T)$); solutions are functions on $\mathbb R^n\times\mathbb R$ constrained only for $t\ge0$; the torus is encoded by $1$-periodicity on $\mathbb R^3$. Definitions come from `Definitions.Def_ClayNavierStokes_defs`.
-- source:
--   C. L. Fefferman, Existence and Smoothness of the Navier–Stokes Equation, Clay Mathematics Institute Millennium Prize Problem description, https://www.claymath.org/wp-content/uploads/2022/06/navierstokes.pdf, p. 2, statement (B); conditions (1), (2), (3), (8), (10), (11) on pp. 1–2; errata (p(x+e_j,t)=p(x,t)).

import Definitions.Def_ClayNavierStokes_defs
import Mathlib

namespace ClayNavierStokes

theorem existence_and_smoothness_periodic (nu : ℝ) (hnu : 0 < nu)
    (u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) (hu₀ : InitialVelocityConditionPeriodic u₀) :
    ∃ v p, NavierStokesExistenceAndSmoothnessPeriodic nu u₀ 0 v p := by sorry

end ClayNavierStokes
