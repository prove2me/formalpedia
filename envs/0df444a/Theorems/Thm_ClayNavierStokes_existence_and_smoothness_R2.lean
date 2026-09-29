-- Prove2me | Theorems.Thm_ClayNavierStokes_existence_and_smoothness_R2
-- name    : ClayNavierStokes.existence_and_smoothness_R2
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T18:42:01.377737+00:00
-- url     : https://prove2.me/theorems/ec3b8412-9033-4f38-a059-076f8cc4bbf5
-- title:
--   Two-dimensional analogue of (A), including Euler ($\nu \ge 0$)
-- statement:
--   Let $\nu\ge0$ and let $u_0:\mathbb R^2\to\mathbb R^2$ be smooth, divergence-free and satisfy the decay condition (4). Then the unforced equations (1)–(3) in $n=2$ have a smooth solution $(u,p)$ on $\mathbb R^2\times[0,\infty)$ with bounded energy (7).
--
--   Fefferman (p. 2) records that the two-dimensional analogues of (A) and (B) are known (Ladyzhenskaya), also for the Euler equations ($\nu=0$).
--
--   **Formalization Note** Time derivatives are one-sided at $t=0$ (taken within $[0,\infty)$, resp. $[0,T)$); solutions are functions on $\mathbb R^n\times\mathbb R$ constrained only for $t\ge0$; the torus is encoded by $1$-periodicity on $\mathbb R^3$. Definitions come from `Definitions.Def_ClayNavierStokes_defs`.
-- source:
--   C. L. Fefferman, Existence and Smoothness of the Navier–Stokes Equation, Clay Mathematics Institute Millennium Prize Problem description, https://www.claymath.org/wp-content/uploads/2022/06/navierstokes.pdf, p. 2, 'In two dimensions, the analogues of assertions (A) and (B) have been known for a long time (Ladyzhenskaya [4]), also for the more difficult case of the Euler equations.'

import Definitions.Def_ClayNavierStokes_defs
import Mathlib

namespace ClayNavierStokes

theorem existence_and_smoothness_R2 (nu : ℝ) (hnu : 0 ≤ nu)
    (u₀ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) (hu₀ : InitialVelocityConditionDecay u₀) :
    ∃ v p, NavierStokesExistenceAndSmoothnessRn nu u₀ 0 v p := by sorry

end ClayNavierStokes
