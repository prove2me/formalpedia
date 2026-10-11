-- Prove2me | Theorems.Thm_BlackScholesModel_call_vega
-- name    : BlackScholesModel.call_vega
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T12:24:02.015246+00:00
-- url     : https://prove2.me/theorems/25bd413d-32c6-4ba4-94b0-131ac65ec0b9
-- title:
--   Volatility derivative of the Black–Scholes call price
-- statement:
--   For positive strike, volatility, spot and time to expiry, differentiate the Black–Scholes call valuation with respect to volatility. The derivative (call vega) is S times the standard normal density at d-plus times the square root of remaining maturity. This is the first conjunct of the published mission milestone BlackScholesModel.vega, isolated because put vega then follows directly by differentiation of put–call parity.
-- source:
--   Black–Scholes option Greeks: analytic vega formula. Exact first conjunct of published Prove2Me mission theorem BlackScholesModel.vega (01767874-b18e-44f8-b79c-2e1d528fb0c8). Supports deriving put vega from call vega and put–call parity, thereby reducing independent analytic calculations.

import Mathlib
import Definitions.Def_BlackScholesModel_Core

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff

namespace BlackScholesModel

theorem call_vega (K r σ T S t : ℝ) (hK : 0 < K) (hσ : 0 < σ) (hS : 0 < S) (ht : t < T) :
    HasDerivAt (fun σ' => callPrice K r σ' T S t)
      (S * stdNormalPDF (dPlus S K r σ (T - t)) * Real.sqrt (T - t)) σ := by
  sorry

end BlackScholesModel
