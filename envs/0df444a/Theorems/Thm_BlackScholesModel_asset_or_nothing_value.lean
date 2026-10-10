-- Prove2me | Theorems.Thm_BlackScholesModel_asset_or_nothing_value
-- name    : BlackScholesModel.asset_or_nothing_value
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:38:56.455588+00:00
-- url     : https://prove2.me/theorems/8c2cb5e6-be8a-46b4-bcf8-b0f47f6bed94
-- title:
--   Asset-or-nothing call and put: $SN(\pm d_+)$
-- statement:
--   Let $K>0$, $\sigma>0$, $S>0$, $t<T$, $r\in\mathbb R$, $\tau=T-t$, and let $S_T=S\exp\big((r-\frac{\sigma^2}2)\tau+\sigma\sqrt\tau Z\big)$ with $Z$ standard normal be the risk-neutral terminal price. The risk-neutral value of a binary option paying one unit of the asset if the spot ends above (respectively below) the strike is
--
--   $$e^{-r\tau}\,\mathbb E\big[S_T\,\mathbf 1_{\{S_T>K\}}\big]=SN(d_+),\qquad e^{-r\tau}\,\mathbb E\big[S_T\,\mathbf 1_{\{S_T<K\}}\big]=SN(-d_+).$$
--
--   Together with the cash-or-nothing values, this splits the call price into an asset-or-nothing call minus $K$ cash-or-nothing calls.
--
--   **Formalization Note** The source's formulas include a dividend yield $q$; this is the non-dividend case $q=0$, with $d_1=d_+$.
-- source:
--   Wikipedia, "Black–Scholes model" (snapshot supplied as Black–Scholes_model.pdf, 22 pp.), https://en.wikipedia.org/wiki/Black%E2%80%93Scholes_model; p. 11 (Binary options: asset-or-nothing call and put), p. 6 (SN(d+) is the present value of the expected asset price given exercise)

import Mathlib
import Definitions.Def_BlackScholesModel_Core

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff

namespace BlackScholesModel

theorem asset_or_nothing_value (K r σ T S t : ℝ) (hK : 0 < K) (hσ : 0 < σ) (hS : 0 < S) (ht : t < T) :
    Real.exp (-r * (T - t))
        * ∫ z in {z | K < terminalPrice S r σ (T - t) z}, terminalPrice S r σ (T - t) z
            ∂(gaussianReal 0 1)
      = S * stdNormalCDF (dPlus S K r σ (T - t)) ∧
    Real.exp (-r * (T - t))
        * ∫ z in {z | terminalPrice S r σ (T - t) z < K}, terminalPrice S r σ (T - t) z
            ∂(gaussianReal 0 1)
      = S * stdNormalCDF (-dPlus S K r σ (T - t)) := by sorry

end BlackScholesModel
