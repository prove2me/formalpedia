-- Prove2me | Theorems.Thm_BlackScholesModel_callPrice_eq_risk_neutral_expectation
-- name    : BlackScholesModel.callPrice_eq_risk_neutral_expectation
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:35:58.296996+00:00
-- url     : https://prove2.me/theorems/cbd02530-704b-4861-9a2c-fc27a5acab5c
-- title:
--   Risk-neutral pricing: $C = e^{-r(T-t)}\,\mathbb E[\max(S_T-K,0)]$
-- statement:
--   Let $K>0$, $\sigma>0$, $S>0$, $t<T$, $r\in\mathbb R$ and $\tau=T-t$. Let $Z$ be a standard normal random variable and let
--
--   $$S_T=S\exp\Big(\big(r-\tfrac{\sigma^2}2\big)\tau+\sigma\sqrt\tau\,Z\Big)$$
--
--   be the terminal stock price under the risk-neutral measure (geometric Brownian motion with drift $r$). Then the Black–Scholes call price is the discounted expected payoff:
--
--   $$C(S,t)=e^{-r\tau}\,\mathbb E\big[\max(S_T-K,0)\big].$$
--
--   **Formalization Note** The expectation is the integral with respect to the standard Gaussian measure on $\mathbb R$ (`gaussianReal 0 1`) of $z\mapsto\max(S_T(z)-K,0)$.
-- source:
--   Wikipedia, "Black–Scholes model" (snapshot supplied as Black–Scholes_model.pdf, 22 pp.), https://en.wikipedia.org/wiki/Black%E2%80%93Scholes_model; p. 6 (Derivations: the option price is the expected value of the discounted payoff under the risk-neutral measure; risk-neutral stock price)

import Mathlib
import Definitions.Def_BlackScholesModel_Core

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff

namespace BlackScholesModel

theorem callPrice_eq_risk_neutral_expectation (K r σ T S t : ℝ) (hK : 0 < K) (hσ : 0 < σ) (hS : 0 < S) (ht : t < T) :
    callPrice K r σ T S t
      = Real.exp (-r * (T - t))
          * ∫ z, max (terminalPrice S r σ (T - t) z - K) 0 ∂(gaussianReal 0 1) := by sorry

end BlackScholesModel
