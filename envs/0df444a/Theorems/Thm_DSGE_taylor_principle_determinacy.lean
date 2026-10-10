-- Prove2me | Theorems.Thm_DSGE_taylor_principle_determinacy
-- name    : DSGE.taylor_principle_determinacy
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:31:18.326837+00:00
-- url     : https://prove2.me/theorems/45eee70c-defe-4456-891c-22cd7642e389
-- title:
--   Taylor principle: determinacy of the New Keynesian model iff $\kappa(\phi_\pi-1)+(1-\beta)\phi_y>0$
-- statement:
--   Consider the deterministic three-equation New Keynesian model (demand, supply and Taylor-rule equations, see the definition file) with parameters
--   $$
--   \sigma > 0, \qquad 0 < \beta < 1, \qquad \kappa > 0, \qquad \phi_\pi \ge 0, \qquad \phi_y \ge 0 .
--   $$
--   The model is determinate — the zero steady state is its only equilibrium in which output gap, inflation and the interest rate all stay bounded — if and only if
--   $$
--   \kappa\,(\phi_\pi - 1) + (1 - \beta)\,\phi_y > 0 .
--   $$
--
--   This is the **Taylor principle** in the form of Bullard and Mitra (2002) and Galí (2008, Ch. 3): the central bank must respond to inflation sufficiently strongly (roughly, raise the nominal rate more than one-for-one with inflation) for the model's equilibrium to be pinned down. It formalises the source's description of the simplified DSGE model as a complete, jointly determined system of output, inflation and the nominal interest rate.
-- source:
--   Wikipedia, "Dynamic stochastic general equilibrium" (uploaded PDF), section "DSGE modeling — Structure" (simplified demand / supply / monetary-policy model) and section "Criticism" (consumption Euler equation paragraph); https://en.wikipedia.org/wiki/Dynamic_stochastic_general_equilibrium; determinacy condition from J. Galí, Monetary Policy, Inflation, and the Business Cycle, Princeton University Press, 2008, Chapter 3 (the basic New Keynesian model under an interest-rate rule); J. Bullard and K. Mitra, Learning about monetary policy rules, J. Monetary Economics 49 (2002) 1105-1129

import Mathlib
import Definitions.Def_DSGE_NK_model

namespace DSGE
theorem taylor_principle_determinacy (σ β κ φπ φy : ℝ)
    (hσ : 0 < σ) (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) :
    IsDeterminate σ β κ φπ φy ↔ 0 < κ * (φπ - 1) + (1 - β) * φy := by sorry
end DSGE
