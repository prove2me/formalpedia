-- Prove2me | Theorems.Thm_DSGE_nk_equilibrium_iff_forward
-- name    : DSGE.nk_equilibrium_iff_forward
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:29:04.278691+00:00
-- url     : https://prove2.me/theorems/d7db7704-9fea-4f36-8cee-31d23b026056
-- title:
--   Forward (state-space) form of the New Keynesian model
-- statement:
--   Let $\sigma \ne 0$ and $\beta \ne 0$, and let $\kappa, \phi_\pi, \phi_y$ be arbitrary reals. Real sequences $(y_t, \pi_t, i_t)_{t\ge0}$ form an equilibrium of the three-equation New Keynesian model (demand, supply and Taylor-rule equations, see the definition file) if and only if, for every $t \ge 0$,
--   $$
--   \begin{aligned}
--   i_t &= \phi_\pi \pi_t + \phi_y y_t,\\
--   \pi_{t+1} &= \frac{\pi_t - \kappa\, y_t}{\beta},\\
--   y_{t+1} &= \Big(1 + \frac{\phi_y}{\sigma} + \frac{\kappa}{\sigma\beta}\Big) y_t + \frac{\phi_\pi - 1/\beta}{\sigma}\,\pi_t .
--   \end{aligned}
--   $$
--
--   In words: once the interest rate is substituted out, the model is the linear recursion $(y_{t+1}, \pi_{t+1})^{\top} = M\,(y_t, \pi_t)^{\top}$ with
--   $M = \begin{pmatrix} 1 + \phi_y/\sigma + \kappa/(\sigma\beta) & (\phi_\pi - 1/\beta)/\sigma \\ -\kappa/\beta & 1/\beta \end{pmatrix}$. This is the state-space form on which the determinacy analysis rests.
-- source:
--   Wikipedia, "Dynamic stochastic general equilibrium" (uploaded PDF), section "DSGE modeling — Structure" (simplified demand / supply / monetary-policy model) and section "Criticism" (consumption Euler equation paragraph); https://en.wikipedia.org/wiki/Dynamic_stochastic_general_equilibrium; state-space form as in J. Galí, Monetary Policy, Inflation, and the Business Cycle, Princeton University Press, 2008, Chapter 3 (the basic New Keynesian model under an interest-rate rule); J. Bullard and K. Mitra, Learning about monetary policy rules, J. Monetary Economics 49 (2002) 1105-1129

import Mathlib
import Definitions.Def_DSGE_NK_model

namespace DSGE
theorem nk_equilibrium_iff_forward (σ β κ φπ φy : ℝ) (hσ : σ ≠ 0) (hβ : β ≠ 0)
    (y π i : ℕ → ℝ) :
    IsNKEquilibrium σ β κ φπ φy y π i ↔
      ∀ t : ℕ,
        i t = φπ * π t + φy * y t ∧
        π (t + 1) = (π t - κ * y t) / β ∧
        y (t + 1) = (1 + φy / σ + κ / (σ * β)) * y t + ((φπ - 1 / β) / σ) * π t := by sorry
end DSGE
