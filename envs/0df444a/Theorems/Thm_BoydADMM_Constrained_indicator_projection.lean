-- Prove2me | Theorems.Thm_BoydADMM_Constrained_indicator_projection
-- name    : BoydADMM.Constrained.indicator_projection
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T02:07:20.578192+00:00
-- url     : https://prove2.me/theorems/a9f55ff2-b2ce-4bc1-8acc-652bb525fc9c
-- title:
--   The indicator-function z-update is Euclidean projection
-- statement:
--   Let $C\subseteq\mathbb R^n$ be nonempty, closed and convex, let $\rho>0$, and let $v\in\mathbb R^n$. For a point $p\in C$, minimizing the indicator-function part of the scaled ADMM $z$-update is equivalent to projecting $v$ onto $C$:
--
--   $$\left[\frac\rho2\|v-p\|_2^2\le\frac\rho2\|v-w\|_2^2\ \text{for all }w\in C\right]\quad\Longleftrightarrow\quad p=\Pi_C(v).$$
--
--   This explains the projection update displayed for constrained optimization on page 33. The source writes $v=x^{k+1}+u^k$.
--
--   **Formalization Note** The indicator is represented by restricting the minimization to $C$. The conclusion uses the published nearest-point predicate; $\rho>0$ and the geometric properties of $C$ make the projection well defined.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), p. 33, (5.1) and scaled z-update; https://doi.org/10.1561/2200000016

import Mathlib
import Definitions.Def_RandomGradFree_Nonsmooth_IsMetricProjection
import Definitions.Def_BoydADMM_Constrained_Geometry

namespace BoydADMM.Constrained

/-- §5, p. 33: the `z`-minimization with the indicator of `C` is Euclidean projection. -/
theorem indicator_projection {n : ℕ} (C : Set (Vec n))
    (hCne : C.Nonempty) (hCclosed : IsClosed C) (hCconvex : Convex ℝ C)
    (ρ : ℝ) (hρ : 0 < ρ) (v p : Vec n) (hp : p ∈ C) :
    (∀ w ∈ C, (ρ / 2) * ‖v - p‖ ^ 2 ≤ (ρ / 2) * ‖v - w‖ ^ 2) ↔
      RandomGradFree.Nonsmooth.IsMetricProjection C v p := by sorry

end BoydADMM.Constrained
