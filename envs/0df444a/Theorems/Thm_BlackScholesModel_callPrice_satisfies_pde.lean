-- Prove2me | Theorems.Thm_BlackScholesModel_callPrice_satisfies_pde
-- name    : BlackScholesModel.callPrice_satisfies_pde
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:43:16.43599+00:00
-- url     : https://prove2.me/theorems/a70e9d3d-3f9e-41d0-9202-4523e6f38931
-- title:
--   Black–Scholes differential equation for the call-price formula
-- statement:
--   The Black–Scholes call valuation formula solves the differential pricing equation on its open time and stock-price domain. This is precisely the second conjunct of the parent theorem, with all nested derivative operators and parameter assumptions unchanged. The analytic route uses the delta, gamma and theta identities and S φ(d+) = K exp(-r τ) φ(d-).
-- source:
--   Source-faithful analytic decomposition of BlackScholesModel.callPrice_solves_black_scholes_equation, theorem UUID 7b9f86c4-ef67-48b5-a89c-e0f23038fec0, in the mission Black–Scholes Model: Pricing Formula, PDE and Greeks. Based on the Black–Scholes formula and equation together with its boundary and payoff conditions (Black and Scholes, 1973; published source cited by parent). Each child exactly preserves a separate clause of the parent with the same assumptions and quantifiers.

import Mathlib
import Definitions.Def_BlackScholesModel_Core

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff

namespace BlackScholesModel

theorem callPrice_satisfies_pde (K r σ T : ℝ) (hK : 0 < K) (hσ : 0 < σ) :
    ∀ S t : ℝ, 0 < S → t < T →
      deriv (fun t' => callPrice K r σ T S t') t
        + 1 / 2 * σ ^ 2 * S ^ 2
            * deriv (fun S' => deriv (fun S'' => callPrice K r σ T S'' t) S') S
        + r * S * deriv (fun S' => callPrice K r σ T S' t) S
        - r * callPrice K r σ T S t = 0 := by
  sorry

end BlackScholesModel
