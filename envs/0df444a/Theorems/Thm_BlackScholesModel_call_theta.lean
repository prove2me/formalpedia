-- Prove2me | Theorems.Thm_BlackScholesModel_call_theta
-- name    : BlackScholesModel.call_theta
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:33:25.788989+00:00
-- url     : https://prove2.me/theorems/59c84e6e-b7bf-4bd0-b855-f354b2dac61d
-- title:
--   Call Theta
-- statement:
--   Let $K>0$, $\sigma>0$, $S>0$, $t<T$ and $r\in\mathbb R$. Then the call price is differentiable in time at $t$, and
--
--   $$\frac{\partial C}{\partial t}(S,t)=-\frac{SN'(d_+)\sigma}{2\sqrt{T-t}}-rKe^{-r(T-t)}N(d_-).$$
-- source:
--   Wikipedia, "Black–Scholes model" (snapshot supplied as Black–Scholes_model.pdf, 22 pp.), https://en.wikipedia.org/wiki/Black%E2%80%93Scholes_model; p. 7 (The Options Greeks, table: Theta, Call)

import Mathlib
import Definitions.Def_BlackScholesModel_Core

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff

namespace BlackScholesModel

theorem call_theta (K r σ T S t : ℝ) (hK : 0 < K) (hσ : 0 < σ) (hS : 0 < S) (ht : t < T) :
    HasDerivAt (fun t' => callPrice K r σ T S t')
      (-(S * stdNormalPDF (dPlus S K r σ (T - t)) * σ) / (2 * Real.sqrt (T - t))
        - r * K * Real.exp (-r * (T - t)) * stdNormalCDF (dMinus S K r σ (T - t))) t := by sorry

end BlackScholesModel
