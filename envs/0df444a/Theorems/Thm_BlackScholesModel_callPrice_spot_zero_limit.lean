-- Prove2me | Theorems.Thm_BlackScholesModel_callPrice_spot_zero_limit
-- name    : BlackScholesModel.callPrice_spot_zero_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T15:38:51.521292+00:00
-- url     : https://prove2.me/theorems/ac04e8ef-8ca0-4181-92b1-a64d7654ee46
-- title:
--   Black–Scholes call price vanishes at zero spot
-- statement:
--   The European call price tends to zero as positive spot tends to zero with positive strike, positive volatility and strictly positive remaining maturity. The normal-CDF arguments d-plus and d-minus both tend to negative infinity and the call-price terms converge to zero. This is the first conjunct of the original published Black–Scholes boundary-limits milestone.
-- source:
--   Exact separated conjunct from BlackScholesModel.callPrice_boundary_limits (58854b69-bba7-4435-8d19-0e28313543e4) of mission e6d32df0-f327-42c2-be41-05cae8e311c8. No new assumptions or altered boundary meaning.

import Mathlib
import Definitions.Def_BlackScholesModel_Core

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff

namespace BlackScholesModel

theorem callPrice_spot_zero_limit (K r σ T t : ℝ) (hK : 0 < K)
    (hσ : 0 < σ) (ht : t < T) :
    Tendsto (fun S => callPrice K r σ T S t) (𝓝[>] 0) (𝓝 0) := by
  sorry

end BlackScholesModel
