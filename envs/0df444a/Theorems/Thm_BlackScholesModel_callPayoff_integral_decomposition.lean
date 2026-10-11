-- Prove2me | Theorems.Thm_BlackScholesModel_callPayoff_integral_decomposition
-- name    : BlackScholesModel.callPayoff_integral_decomposition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T17:04:56.388977+00:00
-- url     : https://prove2.me/theorems/2dc2f1d9-6335-484a-9ec3-46a26544fec3
-- title:
--   Decompose the European call payoff into an asset digital and a cash digital
-- statement:
--   The undiscounted expected European call payoff equals the asset-or-nothing expectation over the in-the-money exercise event less strike multiplied by the probability of that event. This is the identity max(S_T-K,0)=(S_T-K)1_{S_T>K} integrated against the standard Gaussian lognormal price distribution. The proof requires integrability of lognormal terminal stock prices and correct treatment of the boundary S_T=K, and connects already-established digital-option formulas to the full risk-neutral call valuation.
-- source:
--   Exact call payoff decomposition from terminalPrice, Gaussian integrals and finite moments. Substantive prerequisite to published callPrice_eq_risk_neutral_expectation in the Black–Scholes mission.

import Mathlib
import Definitions.Def_BlackScholesModel_Core

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff

namespace BlackScholesModel

theorem callPayoff_integral_decomposition (K r σ τ S : ℝ)
    (hK : 0 < K) (hσ : 0 < σ) (hτ : 0 < τ) (hS : 0 < S) :
    (∫ z, max (terminalPrice S r σ τ z - K) 0
      ∂(gaussianReal 0 1)) =
      (∫ z in {z | K < terminalPrice S r σ τ z},
        terminalPrice S r σ τ z ∂(gaussianReal 0 1)) -
      K * (gaussianReal 0 1).real
        {z | K < terminalPrice S r σ τ z} := by
  sorry

end BlackScholesModel
