-- Prove2me | Theorems.Thm_DSGE_nk_equilibrium_exists_unique
-- name    : DSGE.nk_equilibrium_exists_unique
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:30:09.296977+00:00
-- url     : https://prove2.me/theorems/2880f4e7-3ac0-4070-8c97-e586bbaeed74
-- title:
--   Equilibria are parametrised by initial output gap and inflation
-- statement:
--   Let $\sigma \ne 0$ and $\beta \ne 0$, and let $\kappa, \phi_\pi, \phi_y$ be arbitrary reals. For every pair of prescribed initial values $y_0^{\ast}, \pi_0^{\ast} \in \mathbb R$ there is exactly one equilibrium $(y_t, \pi_t, i_t)_{t \ge 0}$ of the three-equation New Keynesian model with
--   $$
--   y_0 = y_0^{\ast}, \qquad \pi_0 = \pi_0^{\ast}.
--   $$
--   Hence the set of all equilibria is a two-dimensional real vector space, and determinacy is the question of which of these equilibria stay bounded.
-- source:
--   Wikipedia, "Dynamic stochastic general equilibrium" (uploaded PDF), section "DSGE modeling — Structure" (simplified demand / supply / monetary-policy model) and section "Criticism" (consumption Euler equation paragraph); https://en.wikipedia.org/wiki/Dynamic_stochastic_general_equilibrium; J. Galí, Monetary Policy, Inflation, and the Business Cycle, Princeton University Press, 2008, Chapter 3 (the basic New Keynesian model under an interest-rate rule); J. Bullard and K. Mitra, Learning about monetary policy rules, J. Monetary Economics 49 (2002) 1105-1129

import Mathlib
import Definitions.Def_DSGE_NK_model

namespace DSGE
theorem nk_equilibrium_exists_unique (σ β κ φπ φy : ℝ) (hσ : σ ≠ 0) (hβ : β ≠ 0)
    (y₀ π₀ : ℝ) :
    ∃! p : (ℕ → ℝ) × (ℕ → ℝ) × (ℕ → ℝ),
      IsNKEquilibrium σ β κ φπ φy p.1 p.2.1 p.2.2 ∧ p.1 0 = y₀ ∧ p.2.1 0 = π₀ := by sorry
end DSGE
