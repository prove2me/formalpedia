-- Prove2me | Theorems.Thm_BlackScholesModel_call_delta
-- name    : BlackScholesModel.call_delta
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:30:27.856528+00:00
-- url     : https://prove2.me/theorems/85a8f923-4363-4230-aea9-4edb39feddab
-- title:
--   Call Delta: $\partial C/\partial S = N(d_+)$
-- statement:
--   Let $K>0$, $\sigma>0$, $S>0$, $t<T$ and $r\in\mathbb R$. Then the Black–Scholes call price is differentiable in the spot price at $S$, with
--
--   $$\frac{\partial C}{\partial S}(S,t)=N(d_+).$$
--
--   Delta is the hedge ratio of the Black–Scholes replication argument.
-- source:
--   Wikipedia, "Black–Scholes model" (snapshot supplied as Black–Scholes_model.pdf, 22 pp.), https://en.wikipedia.org/wiki/Black%E2%80%93Scholes_model; p. 7 (The Options Greeks, table: Delta, Call)

import Mathlib
import Definitions.Def_BlackScholesModel_Core

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff

namespace BlackScholesModel

theorem call_delta (K r σ T S t : ℝ) (hK : 0 < K) (hσ : 0 < σ) (hS : 0 < S) (ht : t < T) :
    HasDerivAt (fun S' => callPrice K r σ T S' t)
      (stdNormalCDF (dPlus S K r σ (T - t))) S := by sorry

end BlackScholesModel
