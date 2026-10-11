-- Prove2me | Theorems.Thm_BlackScholesModel_call_upper_tail_spot_product
-- name    : BlackScholesModel.call_upper_tail_spot_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T15:59:33.259921+00:00
-- url     : https://prove2.me/theorems/a5ac51b0-38f1-4233-8311-4e4d2419829a
-- title:
--   Spot-weighted Black–Scholes normal upper tail vanishes
-- statement:
--   With positive strike, volatility and fixed time to expiry, spot multiplied by the upper standard-normal tail at the Black–Scholes d-plus argument tends to zero as spot tends to infinity. Although spot grows without bound, d-plus grows logarithmically with spot and Gaussian upper-tail decay dominates every exponential in d-plus. This analytic estimate is the remaining difficult component of the call-price large-spot asymptotic.
-- source:
--   Analytic subproblem extracted without changing the original theorem BlackScholesModel.callPrice_large_spot_limit of mission e6d32df0-f327-42c2-be41-05cae8e311c8. Uses the standard normal upper-tail/Mills inequality and exact dPlus definition.

import Mathlib
import Definitions.Def_BlackScholesModel_Core

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff

namespace BlackScholesModel

theorem call_upper_tail_spot_product (K r σ τ : ℝ) (hK : 0 < K)
    (hσ : 0 < σ) (hτ : 0 < τ) :
    Tendsto (fun S => S * (1 - stdNormalCDF (dPlus S K r σ τ)))
      atTop (𝓝 0) := by
  sorry

end BlackScholesModel
