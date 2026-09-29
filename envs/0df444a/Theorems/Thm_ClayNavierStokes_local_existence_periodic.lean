-- Prove2me | Theorems.Thm_ClayNavierStokes_local_existence_periodic
-- name    : ClayNavierStokes.local_existence_periodic
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T18:45:30.978991+00:00
-- url     : https://prove2.me/theorems/9449c06f-3ba1-4e5d-9c5e-63b3e9c40fe2
-- title:
--   Local-in-time smooth solutions on $\mathbb R^3/\mathbb Z^3$ ($\nu \ge 0$)
-- statement:
--   Let $\nu\ge0$ and let $u_0:\mathbb R^3\to\mathbb R^3$ be smooth, divergence-free and $1$-periodic. Then there is $T>0$ and smooth, spatially $1$-periodic $(u,p)$ on $\mathbb R^3\times[0,T)$ solving the unforced equations (1)–(3) for $0\le t<T$.
--
--   Fefferman (p. 2): local-in-time version of (B), also for $\nu=0$.
--
--   **Formalization Note** Time derivatives are one-sided at $t=0$ (taken within $[0,\infty)$, resp. $[0,T)$); solutions are functions on $\mathbb R^n\times\mathbb R$ constrained only for $t\ge0$; the torus is encoded by $1$-periodicity on $\mathbb R^3$. Definitions come from `Definitions.Def_ClayNavierStokes_defs`.
-- source:
--   C. L. Fefferman, Existence and Smoothness of the Navier–Stokes Equation, Clay Mathematics Institute Millennium Prize Problem description, https://www.claymath.org/wp-content/uploads/2022/06/navierstokes.pdf, p. 2, 'it is known that (A) and (B) hold (also for ν = 0) if the time interval [0, ∞) is replaced by a small time interval [0, T), with T depending on the initial data.'

import Definitions.Def_ClayNavierStokes_defs
import Mathlib

namespace ClayNavierStokes

theorem local_existence_periodic (nu : ℝ) (hnu : 0 ≤ nu)
    (u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) (hu₀ : InitialVelocityConditionPeriodic u₀) :
    ∃ T > 0, ∃ v p, NavierStokesLocalSmoothSolutionPeriodic nu u₀ 0 T v p := by sorry

end ClayNavierStokes
