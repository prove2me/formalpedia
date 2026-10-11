-- Prove2me | Theorems.Thm_BlackScholesModel_terminalPrice_strike_events
-- name    : BlackScholesModel.terminalPrice_strike_events
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T16:30:03.224827+00:00
-- url     : https://prove2.me/theorems/8453997a-6fe1-487b-81a8-ff9fd574f34c
-- title:
--   Strike crossing events of lognormal terminal price
-- statement:
--   For a positive initial spot, strike, volatility and remaining term, the lognormal Black–Scholes terminal stock price exceeds the strike exactly when the standard Gaussian innovation z exceeds minus d-minus, and falls below the strike exactly when z is less than minus d-minus. This is the threshold transformation needed for the published cash-or-nothing and asset-or-nothing digital valuations.
-- source:
--   Exact change of variables from core terminalPrice and dMinus definitions. Supports published cash_or_nothing_value and asset_or_nothing_value milestones of e6d32df0-f327-42c2-be41-05cae8e311c8.

import Mathlib
import Definitions.Def_BlackScholesModel_Core

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff

namespace BlackScholesModel

theorem terminalPrice_strike_events (S K r σ τ : ℝ)
    (hS : 0 < S) (hK : 0 < K) (hσ : 0 < σ) (hτ : 0 < τ) :
    {z : ℝ | K < terminalPrice S r σ τ z} =
      Set.Ioi (-dMinus S K r σ τ) ∧
    {z : ℝ | terminalPrice S r σ τ z < K} =
      Set.Iio (-dMinus S K r σ τ) := by
  sorry

end BlackScholesModel
