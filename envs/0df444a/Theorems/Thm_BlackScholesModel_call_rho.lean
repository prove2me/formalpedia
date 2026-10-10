-- Prove2me | Theorems.Thm_BlackScholesModel_call_rho
-- name    : BlackScholesModel.call_rho
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:34:29.42125+00:00
-- url     : https://prove2.me/theorems/667dcd8a-3149-41af-9ca7-04cd81e50592
-- title:
--   Call Rho: $\partial C/\partial r = K(T-t)e^{-r(T-t)}N(d_-)$
-- statement:
--   Let $K>0$, $\sigma>0$, $S>0$, $t<T$ and $r\in\mathbb R$. Then the call price is differentiable in the interest rate at $r$, and
--
--   $$\frac{\partial C}{\partial r}=K(T-t)e^{-r(T-t)}N(d_-).$$
-- source:
--   Wikipedia, "Black–Scholes model" (snapshot supplied as Black–Scholes_model.pdf, 22 pp.), https://en.wikipedia.org/wiki/Black%E2%80%93Scholes_model; p. 7 (The Options Greeks, table: Rho, Call)

import Mathlib
import Definitions.Def_BlackScholesModel_Core

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff

namespace BlackScholesModel

theorem call_rho (K r σ T S t : ℝ) (hK : 0 < K) (hσ : 0 < σ) (hS : 0 < S) (ht : t < T) :
    HasDerivAt (fun r' => callPrice K r' σ T S t)
      (K * (T - t) * Real.exp (-r * (T - t)) * stdNormalCDF (dMinus S K r σ (T - t))) r := by sorry

end BlackScholesModel
