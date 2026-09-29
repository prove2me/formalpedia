-- Prove2me | Theorems.Thm_ClayNavierStokes_breakdown_R3
-- name    : ClayNavierStokes.breakdown_R3
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T18:41:06.385125+00:00
-- url     : https://prove2.me/theorems/b8f314da-6c84-4144-bffa-b7441d9aa541
-- title:
--   (C) Breakdown of Navier–Stokes solutions on $\mathbb R^3$
-- statement:
--   Let $\nu>0$. There exist a smooth divergence-free $u_0$ on $\mathbb R^3$ and a smooth force $f$ on $\mathbb R^3\times[0,\infty)$ satisfying the decay conditions (4) and (5) for which there is **no** pair $(u,p)$ of smooth functions on $\mathbb R^3\times[0,\infty)$ satisfying
--   $$\partial_t u+(u\cdot\nabla)u=\nu\Delta u-\nabla p+f,\qquad \operatorname{div}u=0,\qquad u(x,0)=u_0(x),$$
--   together with the bounded-energy condition (7).
--
--   This is alternative (C) of the Clay problem; it implies the mission goal.
--
--   **Formalization Note** Time derivatives are one-sided at $t=0$ (taken within $[0,\infty)$, resp. $[0,T)$); solutions are functions on $\mathbb R^n\times\mathbb R$ constrained only for $t\ge0$; the torus is encoded by $1$-periodicity on $\mathbb R^3$. Definitions come from `Definitions.Def_ClayNavierStokes_defs`.
-- source:
--   C. L. Fefferman, Existence and Smoothness of the Navier–Stokes Equation, Clay Mathematics Institute Millennium Prize Problem description, https://www.claymath.org/wp-content/uploads/2022/06/navierstokes.pdf, p. 2, statement (C); conditions (1)–(7) on p. 1.

import Definitions.Def_ClayNavierStokes_defs
import Mathlib

namespace ClayNavierStokes

theorem breakdown_R3 (nu : ℝ) (hnu : 0 < nu) :
    ∃ (u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) (f : EuclideanSpace ℝ (Fin 3) → ℝ → EuclideanSpace ℝ (Fin 3)),
      InitialVelocityConditionDecay u₀ ∧ ForceConditionDecay f ∧
      ¬ ∃ v p, NavierStokesExistenceAndSmoothnessRn nu u₀ f v p := by sorry

end ClayNavierStokes
