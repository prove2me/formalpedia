-- Prove2me | Theorems.Thm_CustomHedge_Exist_proposition_1
-- name    : CustomHedge.Exist.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:17:49.447186+00:00
-- url     : https://prove2.me/theorems/d832687a-ed41-4bf7-abbd-6b537034bc0f
-- title:
--   Proposition 1, p. 9 — every optimal pair of (4) is H* = H*₀ − E_Q[H*₀], G* = G*₀ − E_Q[G*₀] with P-centered (H*₀, G*₀) solving (5)
-- statement:
--   Work in a combined custom hedging market under the standing assumptions. Let $(H^*,G^*)$ be an optimal combined claim pair of the value-centered problem (4), and let $H^*_0=H^*-\mathbb E[H^*]$ and $G^*_0=G^*-\mathbb E[G^*]$ be its $P$-mean-centered versions. Then
--   $$H^*=H^*_0-\mathbb E_Q[H^*_0],\qquad G^*=G^*_0-\mathbb E_Q[G^*_0],\qquad \mathbb E[H^*_0]=\mathbb E[G^*_0]=0,$$
--   and $(H^*_0,G^*_0)$ satisfies the first-order system (5), $P$-a.s.:
--   $$\begin{aligned}H^*_0&=-\mathbb E[\pi-\mathbb E\pi\mid\mathcal F_X]+\mathbb E\big[\tfrac\varrho a\big(1-\tfrac{dQ}{dP}\big)\,\big|\,\mathcal F_X\big]-\mathbb E[G^*_0\mid\mathcal F_X],\\ G^*_0&=-\mathbb E[\pi-\mathbb E\pi\mid\mathcal F_I]+\mathbb E\big[\tfrac\varrho a\big(1-\tfrac{dQ}{dP}\big)\,\big|\,\mathcal F_I\big]-\mathbb E[H^*_0\mid\mathcal F_I].\end{aligned}$$
--
--   This is the necessary condition for optimality; it decomposes each optimal claim into a pure hedging term, a speculative term driven by the market risk premium $1-dQ/dP$, and a cross-claim term. It needs no assumption on the maximal correlation.
--
--   **Formalization Note** The centered claims are taken as $H^*-\mathbb E[H^*]$, as in the paper's proof (p. ec24). Equalities between random variables in (5) hold $P$-almost surely. The added hypothesis $a>0$ is part of the standing assumptions.
-- source:
--   Guiotto & Roncoroni, Combined custom hedging: optimal design, noninsurable exposure, and operational risk management, manuscript OPRE-2019-01-058.R3 (Operations Research 2022), p. 9 (PDF 9), Proposition 1, (4), (5); proof pp. ec23–ec24 (PDF 54–55)

import Mathlib
import Definitions.Def_CustomHedge_Exist_Model

namespace CustomHedge.Exist

open MeasureTheory ProbabilityTheory

variable {Ω EX EY EI : Type*} [MeasurableSpace Ω] [MeasurableSpace EX]
  [MeasurableSpace EY] [MeasurableSpace EI]

/-- Proposition 1 (p. 9). Any optimal pair `(H*, G*)` of the value-centered problem (4) has
the form `H* = H*₀ - E_Q[H*₀]`, `G* = G*₀ - E_Q[G*₀]` with `H*₀ = H* - E[H*]`,
`G*₀ = G* - E[G*]` of zero `P`-mean satisfying the first-order system (5). -/
theorem proposition_1 (M : Market Ω EX EY EI) (hS : M.Standing) (H G : Ω → ℝ)
    (hopt : M.IsOptimal H G) :
    let H₀ : Ω → ℝ := fun ω => H ω - ∫ ω', H ω' ∂M.P
    let G₀ : Ω → ℝ := fun ω => G ω - ∫ ω', G ω' ∂M.P
    (H = fun ω => H₀ ω - M.EQ H₀) ∧ (G = fun ω => G₀ ω - M.EQ G₀) ∧
      ∫ ω, H₀ ω ∂M.P = 0 ∧ ∫ ω, G₀ ω ∂M.P = 0 ∧ M.FirstOrder H₀ G₀ := by sorry

end CustomHedge.Exist
