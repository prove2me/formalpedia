-- Prove2me | Theorems.Thm_ClayNavierStokes_breakdown_periodic
-- name    : ClayNavierStokes.breakdown_periodic
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T18:41:33.09406+00:00
-- url     : https://prove2.me/theorems/015b8baa-a1d4-4c21-8eb3-bd220985d527
-- title:
--   (D) Breakdown of Navier–Stokes solutions on $\mathbb R^3/\mathbb Z^3$
-- statement:
--   Let $\nu>0$. There exist a smooth, divergence-free, $1$-periodic $u_0$ on $\mathbb R^3$ and a smooth force $f$, $1$-periodic in space and satisfying the time-decay condition (9), for which there is **no** pair $(u,p)$ of smooth functions on $\mathbb R^3\times[0,\infty)$, spatially $1$-periodic, satisfying
--   $$\partial_t u+(u\cdot\nabla)u=\nu\Delta u-\nabla p+f,\qquad \operatorname{div}u=0,\qquad u(x,0)=u_0(x).$$
--
--   This is alternative (D) of the Clay problem; it implies the mission goal.
--
--   **Formalization Note** Time derivatives are one-sided at $t=0$ (taken within $[0,\infty)$, resp. $[0,T)$); solutions are functions on $\mathbb R^n\times\mathbb R$ constrained only for $t\ge0$; the torus is encoded by $1$-periodicity on $\mathbb R^3$. Definitions come from `Definitions.Def_ClayNavierStokes_defs`.
-- source:
--   C. L. Fefferman, Existence and Smoothness of the Navier–Stokes Equation, Clay Mathematics Institute Millennium Prize Problem description, https://www.claymath.org/wp-content/uploads/2022/06/navierstokes.pdf, p. 2, statement (D); conditions (1)–(3), (8)–(11) on pp. 1–2; errata.

import Definitions.Def_ClayNavierStokes_defs
import Mathlib

namespace ClayNavierStokes

theorem breakdown_periodic (nu : ℝ) (hnu : 0 < nu) :
    ∃ (u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) (f : EuclideanSpace ℝ (Fin 3) → ℝ → EuclideanSpace ℝ (Fin 3)),
      InitialVelocityConditionPeriodic u₀ ∧ ForceConditionPeriodic f ∧
      ¬ ∃ v p, NavierStokesExistenceAndSmoothnessPeriodic nu u₀ f v p := by sorry

end ClayNavierStokes
