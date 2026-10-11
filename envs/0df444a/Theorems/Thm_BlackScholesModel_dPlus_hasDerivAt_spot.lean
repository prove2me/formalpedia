-- Prove2me | Theorems.Thm_BlackScholesModel_dPlus_hasDerivAt_spot
-- name    : BlackScholesModel.dPlus_hasDerivAt_spot
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T13:52:38.351045+00:00
-- url     : https://prove2.me/theorems/b2d0c7bc-5049-4ec2-ad13-b8d1ac9c4b60
-- title:
--   Spot derivative of the Black–Scholes d-plus argument
-- statement:
--   For positive spot S, strike K, volatility sigma and remaining term tau, the partial derivative of the Black–Scholes d-plus argument with respect to spot is 1/(S sigma sqrt(tau)). The proof uses the logarithmic derivative and the constant denominator. This is the reusable inner derivative needed when differentiating both N(dPlus) and N(dMinus), including delta and gamma, and is consistent with the authoritative dPlus definition.
-- source:
--   Analytic derivative of the dPlus expression defined in BlackScholesModel_Core, supporting the mission's published call_delta, gamma and spot-sensitivity milestones. Derivable by elementary chain differentiation and positivity assumptions; no weakening or change to the parent results.

import Mathlib
import Definitions.Def_BlackScholesModel_Core

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff

namespace BlackScholesModel

theorem dPlus_hasDerivAt_spot (S K r σ τ : ℝ)
    (hS : 0 < S) (hK : 0 < K) (hσ : 0 < σ) (hτ : 0 < τ) :
    HasDerivAt (fun s => dPlus s K r σ τ)
      (1 / (S * σ * Real.sqrt τ)) S := by
  sorry

end BlackScholesModel
