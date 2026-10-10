-- Prove2me | Theorems.Thm_BlackScholesModel_cash_or_nothing_value
-- name    : BlackScholesModel.cash_or_nothing_value
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:38:11.776594+00:00
-- url     : https://prove2.me/theorems/075c92a7-57d4-44a3-b0d6-31a03d6f8ac2
-- title:
--   Cash-or-nothing call and put: $e^{-r(T-t)}N(\pm d_-)$
-- statement:
--   Let $K>0$, $\sigma>0$, $S>0$, $t<T$, $r\in\mathbb R$, $\tau=T-t$, and let $S_T=S\exp\big((r-\frac{\sigma^2}2)\tau+\sigma\sqrt\tau Z\big)$ with $Z$ standard normal be the risk-neutral terminal price. The risk-neutral value of a binary option paying one unit of cash if the spot ends above (respectively below) the strike is
--
--   $$e^{-r\tau}\,\mathbb Q(S_T>K)=e^{-r\tau}N(d_-),\qquad e^{-r\tau}\,\mathbb Q(S_T<K)=e^{-r\tau}N(-d_-).$$
--
--   In particular $N(d_-)$ is the risk-neutral probability that the call is exercised.
--
--   **Formalization Note** The source's binary-option formulas include a dividend yield $q$; this is the non-dividend case $q=0$ of the base model, with $d_2=d_-$.
-- source:
--   Wikipedia, "Black–Scholes model" (snapshot supplied as Black–Scholes_model.pdf, 22 pp.), https://en.wikipedia.org/wiki/Black%E2%80%93Scholes_model; p. 11 (Binary options: cash-or-nothing call and put), p. 6 (N(d−) is the risk-neutral probability of exercise)

import Mathlib
import Definitions.Def_BlackScholesModel_Core

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff

namespace BlackScholesModel

theorem cash_or_nothing_value (K r σ T S t : ℝ) (hK : 0 < K) (hσ : 0 < σ) (hS : 0 < S) (ht : t < T) :
    Real.exp (-r * (T - t)) * (gaussianReal 0 1).real {z | K < terminalPrice S r σ (T - t) z}
      = Real.exp (-r * (T - t)) * stdNormalCDF (dMinus S K r σ (T - t)) ∧
    Real.exp (-r * (T - t)) * (gaussianReal 0 1).real {z | terminalPrice S r σ (T - t) z < K}
      = Real.exp (-r * (T - t)) * stdNormalCDF (-dMinus S K r σ (T - t)) := by sorry

end BlackScholesModel
