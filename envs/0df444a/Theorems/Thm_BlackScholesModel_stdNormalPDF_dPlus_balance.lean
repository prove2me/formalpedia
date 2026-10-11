-- Prove2me | Theorems.Thm_BlackScholesModel_stdNormalPDF_dPlus_balance
-- name    : BlackScholesModel.stdNormalPDF_dPlus_balance
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T12:46:42.179989+00:00
-- url     : https://prove2.me/theorems/e18693f5-1d41-44ff-8afb-b18c580650e9
-- title:
--   Gaussian density balance identity in the Black–Scholes formula
-- statement:
--   For positive spot, strike, volatility and time to expiry, the Black–Scholes normal densities satisfy S φ(d+) = K e^{-rτ} φ(d−). This exact analytic cancellation follows from d−=d+−σ√τ and the definitions of d± and the normal density. It is a central bridge for deriving call delta, gamma, theta and vega from the call-price formula without duplicating exponential cancellations.
-- source:
--   Source-faithful analytic lemma for the Black–Scholes pricing formula and option Greeks, in the mission Black–Scholes Model: Pricing Formula, PDE and Greeks (e6d32df0-f327-42c2-be41-05cae8e311c8). Mathematical identity S φ(d+) = K e^{-rτ} φ(d−) follows from the supplied d± and normal PDF formulas and is needed in call delta, gamma, rho, theta and vega derivations.

import Mathlib
import Definitions.Def_BlackScholesModel_Core

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff

namespace BlackScholesModel

theorem stdNormalPDF_dPlus_balance
    (S K r σ τ : ℝ) (hS : 0 < S) (hK : 0 < K) (hσ : 0 < σ) (hτ : 0 < τ) :
    S * stdNormalPDF (dPlus S K r σ τ) =
      K * Real.exp (-r * τ) * stdNormalPDF (dMinus S K r σ τ) := by
  sorry

end BlackScholesModel
