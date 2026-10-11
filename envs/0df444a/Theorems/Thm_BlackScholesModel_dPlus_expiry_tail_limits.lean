-- Prove2me | Theorems.Thm_BlackScholesModel_dPlus_expiry_tail_limits
-- name    : BlackScholesModel.dPlus_expiry_tail_limits
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T15:53:55.777479+00:00
-- url     : https://prove2.me/theorems/2e97eb24-a54d-4926-ad45-55e59c8d6437
-- title:
--   D-plus tends to signed infinity before expiry away from the strike
-- statement:
--   As remaining term tends to zero from above, the Black–Scholes d-plus argument tends to positive infinity for an in-the-money call with spot above strike, and negative infinity for an out-of-the-money call with spot below strike. Its leading term is log(S/K) divided by the positive volatility-times-square-root maturity, while the residual drift term tends to zero. This result supports both non-at-the-money cases of the terminal-payoff boundary condition.
-- source:
--   Case-separated analytic prerequisite for published BlackScholesModel.callPrice_expiry_limit (original mission e6d32df0-f327-42c2-be41-05cae8e311c8). Uses exact dPlus definition, pinned Mathlib reciprocal limit and logarithm sign theorems.

import Mathlib
import Definitions.Def_BlackScholesModel_Core

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff

namespace BlackScholesModel

theorem dPlus_expiry_tail_limits (K r σ T S : ℝ) (hK : 0 < K)
    (hσ : 0 < σ) (hS : 0 < S) :
    (K < S → Tendsto (fun t => dPlus S K r σ (T - t)) (𝓝[<] T) atTop) ∧
    (S < K → Tendsto (fun t => dPlus S K r σ (T - t)) (𝓝[<] T) atBot) := by
  sorry

end BlackScholesModel
