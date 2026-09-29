-- Prove2me | Theorems.Thm_ClayNavierStokes_existence_and_smoothness_R3
-- name    : ClayNavierStokes.existence_and_smoothness_R3
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T18:36:27.1277+00:00
-- url     : https://prove2.me/theorems/a625f076-07e0-4b4e-857a-074f3ab5175e
-- title:
--   (A) Existence and smoothness of Navier–Stokes solutions on $\mathbb R^3$
-- statement:
--   Let $\nu>0$ and let $u_0:\mathbb R^3\to\mathbb R^3$ be smooth and divergence-free with $|\partial_x^\alpha u_0(x)|\le C_{\alpha K}(1+|x|)^{-K}$ for all $\alpha,K$. Then there exist smooth $u:\mathbb R^3\times[0,\infty)\to\mathbb R^3$ and $p:\mathbb R^3\times[0,\infty)\to\mathbb R$ with
--   $$\partial_t u+(u\cdot\nabla)u=\nu\Delta u-\nabla p,\qquad \operatorname{div}u=0,\qquad u(x,0)=u_0(x),$$
--   and $\int_{\mathbb R^3}|u(x,t)|^2dx<C$ for all $t\ge0$.
--
--   This is alternative (A) of the Clay problem; it implies the mission goal.
--
--   **Formalization Note** Time derivatives are one-sided at $t=0$ (taken within $[0,\infty)$, resp. $[0,T)$); solutions are functions on $\mathbb R^n\times\mathbb R$ constrained only for $t\ge0$; the torus is encoded by $1$-periodicity on $\mathbb R^3$. Definitions come from `Definitions.Def_ClayNavierStokes_defs`.
-- source:
--   C. L. Fefferman, Existence and Smoothness of the Navier–Stokes Equation, Clay Mathematics Institute Millennium Prize Problem description, https://www.claymath.org/wp-content/uploads/2022/06/navierstokes.pdf, p. 2, statement (A); conditions (1), (2), (3), (4), (6), (7) on p. 1.

import Definitions.Def_ClayNavierStokes_defs
import Mathlib

namespace ClayNavierStokes

theorem existence_and_smoothness_R3 (nu : ℝ) (hnu : 0 < nu)
    (u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) (hu₀ : InitialVelocityConditionDecay u₀) :
    ∃ v p, NavierStokesExistenceAndSmoothnessRn nu u₀ 0 v p := by sorry

end ClayNavierStokes
