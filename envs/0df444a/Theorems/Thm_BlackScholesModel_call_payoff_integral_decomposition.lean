-- Prove2me | Theorems.Thm_BlackScholesModel_call_payoff_integral_decomposition
-- name    : BlackScholesModel.call_payoff_integral_decomposition
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T12:26:52.641225+00:00
-- url     : https://prove2.me/theorems/e74ec012-8d27-454a-be66-fc8ca9cbc031
-- title:
--   Risk-neutral call payoff as asset-or-nothing less strike-weighted digital probability
-- statement:
--   For the Black–Scholes lognormal terminal stock price, decompose the European call payoff (S_T-K)^+ = 1_{S_T>K} S_T - K 1_{S_T>K} and integrate against the standard Gaussian shock law. The expectation of the nonnegative payoff equals the asset-or-nothing first moment on the in-the-money region minus the strike multiplied by that region's probability. This decomposition includes all required integrability and measure-theoretic conditions and supplies the bridge from separately published asset-or-nothing and cash-or-nothing valuation results to the risk-neutral call valuation formula.
-- source:
--   Source-faithful decomposition of BlackScholesModel.callPrice_eq_risk_neutral_expectation (cbd02530-704b-4861-9a2c-fc27a5acab5c), using the standard decomposition (x-K)^+ = x 1_{x>K} - K 1_{x>K} and the mission's published asset-or-nothing and cash-or-nothing milestones.

import Mathlib
import Definitions.Def_BlackScholesModel_Core

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff

namespace BlackScholesModel

theorem call_payoff_integral_decomposition (K r σ T S t : ℝ)
    (hK : 0 < K) (hσ : 0 < σ) (hS : 0 < S) (ht : t < T) :
    (∫ z, max (terminalPrice S r σ (T - t) z - K) 0 ∂(gaussianReal 0 1))
      = (∫ z in {z | K < terminalPrice S r σ (T - t) z},
          terminalPrice S r σ (T - t) z ∂(gaussianReal 0 1))
        - K * (gaussianReal 0 1).real {z | K < terminalPrice S r σ (T - t) z} := by
  sorry

end BlackScholesModel
