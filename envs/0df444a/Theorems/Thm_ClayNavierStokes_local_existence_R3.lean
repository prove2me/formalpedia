-- Prove2me | Theorems.Thm_ClayNavierStokes_local_existence_R3
-- name    : ClayNavierStokes.local_existence_R3
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T18:43:15.668987+00:00
-- url     : https://prove2.me/theorems/36994bd5-1632-4c58-98e6-3dde33c9f5a9
-- title:
--   Local-in-time smooth solutions on $\mathbb R^3$ ($\nu \ge 0$)
-- statement:
--   Let $\nu\ge0$ and let $u_0:\mathbb R^3\to\mathbb R^3$ be smooth, divergence-free and satisfy (4). Then there is $T>0$ (depending on the data) and smooth $(u,p)$ on $\mathbb R^3\times[0,T)$ solving the unforced equations (1)–(3) for $0\le t<T$, with $\int|u(x,t)|^2dx<C$ for $0\le t<T$.
--
--   Fefferman (p. 2): "(A) and (B) hold (also for $\nu=0$) if the time interval $[0,\infty)$ is replaced by a small time interval $[0,T)$, with $T$ depending on the initial data."
--
--   **Formalization Note** Time derivatives are one-sided at $t=0$ (taken within $[0,\infty)$, resp. $[0,T)$); solutions are functions on $\mathbb R^n\times\mathbb R$ constrained only for $t\ge0$; the torus is encoded by $1$-periodicity on $\mathbb R^3$. Definitions come from `Definitions.Def_ClayNavierStokes_defs`.
-- source:
--   C. L. Fefferman, Existence and Smoothness of the Navier–Stokes Equation, Clay Mathematics Institute Millennium Prize Problem description, https://www.claymath.org/wp-content/uploads/2022/06/navierstokes.pdf, p. 2, 'it is known that (A) and (B) hold (also for ν = 0) if the time interval [0, ∞) is replaced by a small time interval [0, T), with T depending on the initial data.'

import Definitions.Def_ClayNavierStokes_defs
import Mathlib

namespace ClayNavierStokes

theorem local_existence_R3 (nu : ℝ) (hnu : 0 ≤ nu)
    (u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) (hu₀ : InitialVelocityConditionDecay u₀) :
    ∃ T > 0, ∃ v p, NavierStokesLocalSmoothSolutionRn nu u₀ 0 T v p := by sorry

end ClayNavierStokes
