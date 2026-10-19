-- Prove2me | Theorems.Thm_CostlyPriceInterp_MarketEq_conditional_variance
-- name    : CostlyPriceInterp.MarketEq.conditional_variance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:20:34.666492+00:00
-- url     : https://prove2.me/theorems/3699c063-0792-4669-8b0e-cdf768067bc0
-- title:
--   Equation (17), p. 18 — Var(Ṽ | s̃_i, s̃_{p,i}, z̃_i) = (τ_v + τ_ε + τ_p)^{−1} + τ_ξ^{−1}
-- statement:
--   Assume the standing assumptions $\tau_v,\tau_\xi,\tau_\varepsilon,\tau_e,\tau_u,\tau_\eta,\gamma>0$ and let $\alpha\in\mathbb R$. Write $\mathrm{Var}(\tilde V\mid S) = \tau_v^{-1} - c^\top\Sigma(\alpha)^{-1}c + \tau_\xi^{-1}$ for the conditional variance of the payoff $\tilde V = \tilde v + \tilde\xi$ given investor $i$'s signals $S = (\tilde s_i,\tilde s_{p,i},\tilde z_i)$, and $\tau_p = \tau_p(\alpha)$ for the precision (15). Then
--   $$\mathrm{Var}(\tilde V\mid \tilde s_i,\tilde s_{p,i},\tilde z_i) = (\tau_v+\tau_\varepsilon+\tau_p)^{-1} + \tau_\xi^{-1},$$
--   and in particular this conditional variance is strictly positive.
--
--   The identity says that the three signals together carry precision $\tau_\varepsilon + \tau_p$ about $\tilde v$; its positivity makes the CARA demand (8) well defined.
-- source:
--   Vives & Yang, Costly Interpretation of Asset Prices, SSRN working paper 2763813 (September 2018 version), p. 18 (PDF 20), eqs. (15) and (17)

import Mathlib
import Definitions.Def_CostlyPriceInterp_MarketEq_Model

namespace CostlyPriceInterp.MarketEq

/-- Equation (17), p. 18 (PDF 20): Var(Ṽ | s̃_i, s̃_{p,i}, z̃_i) = (τ_v + τ_ε + τ_p)⁻¹ + τ_ξ⁻¹, with τ_p
of (15); in particular it is positive. -/
theorem conditional_variance (P : Params) (hP : P.Standing) (α : ℝ) :
    condVarV P α = (P.tv + P.teps + tauP P α)⁻¹ + P.txi⁻¹ ∧ 0 < condVarV P α := by sorry
end CostlyPriceInterp.MarketEq
