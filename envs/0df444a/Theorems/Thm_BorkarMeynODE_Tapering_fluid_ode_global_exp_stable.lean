-- Prove2me | Theorems.Thm_BorkarMeynODE_Tapering_fluid_ode_global_exp_stable
-- name    : BorkarMeynODE.Tapering.fluid_ode_global_exp_stable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T19:41:38.652068+00:00
-- url     : https://prove2.me/theorems/596be7a1-1455-4cff-b4cc-3ccfb810031f
-- title:
--   Lemma 4.1 — under (A1) the fluid-limit ODE is globally exponentially asymptotically stable
-- statement:
--   Let $h:\mathbb R^d\to\mathbb R^d$ and $h_\infty:\mathbb R^d\to\mathbb R^d$ satisfy assumption (A1): $h$ is Lipschitz, $h(rx)/r\to h_\infty(x)$ as $r\to\infty$ for every $x$, and the origin is an asymptotically stable equilibrium of the fluid-limit ODE
--   $$
--   \dot x(t) = h_\infty(x(t)). \tag{1.5}
--   $$
--   Then (1.5) is globally exponentially asymptotically stable at the origin: $h_\infty(0)=0$, and there exist constants $b$ and $\delta>0$ such that every solution of (1.5) satisfies
--   $$
--   \|x(t)\| \le b\,e^{-\delta t}\,\|x(0)\|, \qquad t\ge0 .
--   $$
--
--   The lemma upgrades the local stability assumed in (A1) to a global, exponential statement. It is what makes the fluid limit a useful comparison for the rescaled recursion whatever the size of the initial rescaled state.
-- source:
--   Borkar and Meyn, The O.D.E. Method for Convergence of Stochastic Approximation and Reinforcement Learning, SIAM J. Control Optim. 38(2) (2000), p. 460, Lemma 4.1

import Mathlib
import Definitions.Def_BorkarMeynODE_Tapering_ODEStability
import Definitions.Def_BorkarMeynODE_Tapering_AssumptionA1

namespace BorkarMeynODE.Tapering

/-- **Lemma 4.1** (Borkar–Meyn 2000, p. 460). Under (A1), the fluid-limit ODE (1.5)
`ẋ = h_∞(x)` is globally exponentially asymptotically stable at the origin: `h_∞(0) = 0` and
there are `b` and `δ > 0` with `‖x(t)‖ ≤ b e^{−δ t} ‖x(0)‖` for every solution and every
`t ≥ 0`. -/
theorem fluid_ode_global_exp_stable {d : ℕ}
    (h hInf : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hA1 : AssumptionA1 h hInf) :
    IsGloballyExpStable hInf 0 := by sorry

end BorkarMeynODE.Tapering
