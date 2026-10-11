-- Prove2me | Theorems.Thm_BlackScholesModel_callPrice_large_spot_limit
-- name    : BlackScholesModel.callPrice_large_spot_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T15:38:50.136118+00:00
-- url     : https://prove2.me/theorems/551e1b97-0b2e-48ae-a5ff-4bf435c5d86a
-- title:
--   Black–Scholes call price large-spot intrinsic asymptotic
-- statement:
--   As spot tends to positive infinity with fixed strike, rate, volatility and positive time to expiry, the Black–Scholes call price minus spot less discounted strike tends to zero. The result requires Gaussian tail estimates because a vanishing normal upper-tail probability is multiplied by an unbounded spot. This is exactly the second conjunct of the published boundary milestone.
-- source:
--   Exact separated conjunct from BlackScholesModel.callPrice_boundary_limits (58854b69-bba7-4435-8d19-0e28313543e4) of mission e6d32df0-f327-42c2-be41-05cae8e311c8. No new assumptions or altered boundary meaning.

import Mathlib
import Definitions.Def_BlackScholesModel_Core

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff

namespace BlackScholesModel

theorem callPrice_large_spot_limit (K r σ T t : ℝ) (hK : 0 < K)
    (hσ : 0 < σ) (ht : t < T) :
    Tendsto (fun S => callPrice K r σ T S t -
        (S - K * Real.exp (-r * (T - t)))) atTop (𝓝 0) := by
  sorry

end BlackScholesModel
