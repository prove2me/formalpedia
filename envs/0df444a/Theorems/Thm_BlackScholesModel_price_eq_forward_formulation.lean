-- Prove2me | Theorems.Thm_BlackScholesModel_price_eq_forward_formulation
-- name    : BlackScholesModel.price_eq_forward_formulation
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:28:51.16798+00:00
-- url     : https://prove2.me/theorems/67c53231-599b-403c-862b-328d0a7f784d
-- title:
--   Alternative (Black '76) formulation of the call and put prices
-- statement:
--   Let $K>0$, $\sigma>0$, $S>0$, $t<T$ and $r\in\mathbb R$, and put $\tau=T-t$, $D=e^{-r\tau}$ (discount factor) and $F=e^{r\tau}S$ (forward price). With the forward-form parameters $d_\pm=\frac{1}{\sigma\sqrt\tau}\big[\ln\frac FK\pm\frac12\sigma^2\tau\big]$, the Black–Scholes prices satisfy
--
--   $$C(S,t)=D\,[N(d_+)F-N(d_-)K],\qquad P(S,t)=D\,[N(-d_-)K-N(-d_+)F].$$
--
--   This is the special case of the Black '76 formula used in the Interpretation section, where $DN(d_+)F$ and $DN(d_-)K$ are the present values of an asset-or-nothing and a cash-or-nothing call.
-- source:
--   Wikipedia, "Black–Scholes model" (snapshot supplied as Black–Scholes_model.pdf, 22 pp.), https://en.wikipedia.org/wiki/Black%E2%80%93Scholes_model; pp. 4–5 (Alternative formulation)

import Mathlib
import Definitions.Def_BlackScholesModel_Core

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff

namespace BlackScholesModel

theorem price_eq_forward_formulation (K r σ T S t : ℝ) (hK : 0 < K) (hσ : 0 < σ) (hS : 0 < S) (ht : t < T) :
    callPrice K r σ T S t
        = callPriceFwd (Real.exp (-r * (T - t))) (Real.exp (r * (T - t)) * S) K σ (T - t) ∧
    putPrice K r σ T S t
        = putPriceFwd (Real.exp (-r * (T - t))) (Real.exp (r * (T - t)) * S) K σ (T - t) := by sorry

end BlackScholesModel
