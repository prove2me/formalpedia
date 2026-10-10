-- Prove2me | Theorems.Thm_BlackScholesModel_put_rho
-- name    : BlackScholesModel.put_rho
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:35:33.384319+00:00
-- url     : https://prove2.me/theorems/3ddd8d34-2492-41b7-9e5f-59ea78b473c9
-- title:
--   Put Rho: $\partial P/\partial r = -K(T-t)e^{-r(T-t)}N(-d_-)$
-- statement:
--   Let $K>0$, $\sigma>0$, $S>0$, $t<T$ and $r\in\mathbb R$. Then the put price is differentiable in the interest rate at $r$, and
--
--   $$\frac{\partial P}{\partial r}=-K(T-t)e^{-r(T-t)}N(-d_-).$$
-- source:
--   Wikipedia, "Black–Scholes model" (snapshot supplied as Black–Scholes_model.pdf, 22 pp.), https://en.wikipedia.org/wiki/Black%E2%80%93Scholes_model; p. 7 (The Options Greeks, table: Rho, Put)

import Mathlib
import Definitions.Def_BlackScholesModel_Core

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff

namespace BlackScholesModel

theorem put_rho (K r σ T S t : ℝ) (hK : 0 < K) (hσ : 0 < σ) (hS : 0 < S) (ht : t < T) :
    HasDerivAt (fun r' => putPrice K r' σ T S t)
      (-(K * (T - t) * Real.exp (-r * (T - t)) * stdNormalCDF (-dMinus S K r σ (T - t)))) r := by sorry

end BlackScholesModel
