-- Prove2me | Theorems.Thm_BorkarMeynODE_Tapering_scaled_ode_small_on_window
-- name    : BorkarMeynODE.Tapering.scaled_ode_small_on_window
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T19:43:44.373261+00:00
-- url     : https://prove2.me/theorems/7a5c5193-07fc-4788-9cce-6129c59a54be
-- title:
--   Lemma 4.4 — for large scale $r$, solutions of $\dot x=h_r(x)$ from the unit ball are $\epsilon$-small on $[T,T+1]$
-- statement:
--   Assume (A1) for $(h,h_\infty)$ and write $h_r(x)=h(rx)/r$. For every $\epsilon>0$ there exist $T\ge0$ and $R<\infty$ such that for every $r>R$ and every solution of the scaled ODE
--   $$
--   \dot x(t) = h_r(x(t)) \tag{1.4}
--   $$
--   with $\|x(0)\|\le1$,
--   $$
--   \|x(t)\| \le \epsilon, \qquad t\in[T,T+1] .
--   $$
--
--   This transfers the global stability of the fluid limit (Lemma 4.1) to the scaled ODEs with large scale, uniformly over initial conditions in the unit ball; in the proof of Theorem 2.1 (i) it yields the contraction of $\|X(m(j))\|$ over one block when the iterate is large.
--
--   **Formalization Note** The page assumes "(A1) and (A2)"; (A2) concerns the noise $M$, which does not occur in the statement, so it is omitted. $T\ge0$ is implicit on the page, since solutions are considered for $t\ge0$.
-- source:
--   Borkar and Meyn, The O.D.E. Method for Convergence of Stochastic Approximation and Reinforcement Learning, SIAM J. Control Optim. 38(2) (2000), p. 462, Lemma 4.4

import Mathlib
import Definitions.Def_BorkarMeynODE_Tapering_ODEStability
import Definitions.Def_BorkarMeynODE_Tapering_AssumptionA1

namespace BorkarMeynODE.Tapering

/-- **Lemma 4.4** (Borkar–Meyn 2000, p. 462). Under (A1): for every `ε > 0` there are
`T ≥ 0` and `R` such that, for every `r > R` and every solution `x` of the scaled ODE (1.4)
`ẋ = h_r(x)` with `‖x(0)‖ ≤ 1`, `‖x(t)‖ ≤ ε` for all `t ∈ [T, T + 1]`.
The page also lists (A2), which concerns the noise `M`; `M` does not occur in this
statement, so (A2) is omitted. `T ≥ 0` is implicit on the page (solutions live on `t ≥ 0`). -/
theorem scaled_ode_small_on_window {d : ℕ}
    (h hInf : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hA1 : AssumptionA1 h hInf) :
    ∀ ε : ℝ, 0 < ε → ∃ T R : ℝ, 0 ≤ T ∧
      ∀ r : ℝ, R < r → ∀ x : ℝ → EuclideanSpace ℝ (Fin d),
        IsODESolution (scaledField h r) x → ‖x 0‖ ≤ 1 →
          ∀ t ∈ Set.Icc T (T + 1), ‖x t‖ ≤ ε := by sorry

end BorkarMeynODE.Tapering
