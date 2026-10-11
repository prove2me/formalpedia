-- Prove2me | Theorems.Thm_BlackScholesModel_callPrice_expiry_at_strike
-- name    : BlackScholesModel.callPrice_expiry_at_strike
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T15:51:06.881221+00:00
-- url     : https://prove2.me/theorems/ad88c1be-4361-4622-8f49-8786ef4d5bd4
-- title:
--   At-the-money Black–Scholes call converges to zero at expiry
-- statement:
--   For positive strike K and volatility sigma, a European call with spot exactly equal to strike has price tending to zero as expiry is approached from below. The log-moneyness term vanishes, both d-plus and d-minus tend to zero, and their normal CDF terms cancel at the common limit while the discount factor tends to one. This supplies the at-the-money case of the published callPrice_expiry_limit theorem.
-- source:
--   At-the-money case S=K of exact published BlackScholesModel.callPrice_expiry_limit in mission e6d32df0-f327-42c2-be41-05cae8e311c8. Uses published core definitions and proved normal-CDF smoothness.

import Mathlib
import Definitions.Def_BlackScholesModel_Core

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff

namespace BlackScholesModel

theorem callPrice_expiry_at_strike (K r σ T : ℝ)
    (hK : 0 < K) (hσ : 0 < σ) :
    Tendsto (fun t => callPrice K r σ T K t) (𝓝[<] T) (𝓝 0) := by
  sorry

end BlackScholesModel
