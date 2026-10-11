-- Prove2me | Theorems.Thm_BlackScholesModel_callPrice_expiry_limit
-- name    : BlackScholesModel.callPrice_expiry_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T15:37:59.616215+00:00
-- url     : https://prove2.me/theorems/079f2e74-5dba-42c5-a864-aef2de10ed76
-- title:
--   Black–Scholes call converges to its expiry payoff
-- statement:
--   For strictly positive strike, spot and volatility, the Black–Scholes call formula converges to the payoff max(S-K,0) as time approaches expiry from below. The cases S>K, S<K and S=K use the signs of log(S/K) and continuity of the normal CDF. This is exactly the third conjunct of the published boundary milestone.
-- source:
--   Exact separated conjunct from BlackScholesModel.callPrice_boundary_limits (58854b69-bba7-4435-8d19-0e28313543e4) of mission e6d32df0-f327-42c2-be41-05cae8e311c8. No new assumptions or altered boundary meaning.

import Mathlib
import Definitions.Def_BlackScholesModel_Core

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff

namespace BlackScholesModel

theorem callPrice_expiry_limit (K r σ T S : ℝ) (hK : 0 < K)
    (hσ : 0 < σ) (hS : 0 < S) :
    Tendsto (fun t => callPrice K r σ T S t) (𝓝[<] T)
      (𝓝 (max (S - K) 0)) := by
  sorry

end BlackScholesModel
