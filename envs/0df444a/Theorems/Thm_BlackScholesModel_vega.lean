-- Prove2me | Theorems.Thm_BlackScholesModel_vega
-- name    : BlackScholesModel.vega
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:32:46.527509+00:00
-- url     : https://prove2.me/theorems/01767874-b18e-44f8-b79c-2e1d528fb0c8
-- title:
--   Vega: $\partial V/\partial\sigma = SN'(d_+)\sqrt{T-t}$ for calls and puts
-- statement:
--   Let $K>0$, $\sigma>0$, $S>0$, $t<T$ and $r\in\mathbb R$. Then the call and put prices are differentiable in the volatility at $\sigma$, and
--
--   $$\frac{\partial C}{\partial\sigma}=\frac{\partial P}{\partial\sigma}=SN'(d_+)\sqrt{T-t}.$$
-- source:
--   Wikipedia, "Black–Scholes model" (snapshot supplied as Black–Scholes_model.pdf, 22 pp.), https://en.wikipedia.org/wiki/Black%E2%80%93Scholes_model; p. 7 (The Options Greeks, table: Vega)

import Mathlib
import Definitions.Def_BlackScholesModel_Core

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff

namespace BlackScholesModel

theorem vega (K r σ T S t : ℝ) (hK : 0 < K) (hσ : 0 < σ) (hS : 0 < S) (ht : t < T) :
    HasDerivAt (fun σ' => callPrice K r σ' T S t)
      (S * stdNormalPDF (dPlus S K r σ (T - t)) * Real.sqrt (T - t)) σ ∧
    HasDerivAt (fun σ' => putPrice K r σ' T S t)
      (S * stdNormalPDF (dPlus S K r σ (T - t)) * Real.sqrt (T - t)) σ := by sorry

end BlackScholesModel
