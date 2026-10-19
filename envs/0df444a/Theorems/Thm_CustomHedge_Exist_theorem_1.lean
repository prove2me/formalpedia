-- Prove2me | Theorems.Thm_CustomHedge_Exist_theorem_1
-- name    : CustomHedge.Exist.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:18:00.295464+00:00
-- url     : https://prove2.me/theorems/c3810ea8-9cae-4c48-aba2-46eea3cc1693
-- title:
--   Theorem 1, p. 11 — if r_XI < 1, the optimal combined claim pair of (4) exists, is unique, and H*₀ solves (7)
-- statement:
--   Work in a combined custom hedging market under the standing assumptions (probability $P$; random elements $X,Y,I$; position $\pi=\pi(X,Y)\in L^2$; pricing kernel $dQ/dP>0$ a.s., of mean one, in $L^2$; $\varrho\ge0$, $a>0$). Suppose the claimable term $X$ and the index $I$ have maximal correlation
--   $$r_{XI}<1 .$$
--   Then:
--
--   1. an optimal combined claim pair $(H^*,G^*)$ of the value-centered problem (4) exists;
--   2. it is unique: any two optimal pairs agree $P$-a.s., and so do the resulting combined custom hedges $H^*+G^*$;
--   3. the value-centered optimal claim $H^*_0=H^*-\mathbb E[H^*]$ solves the fixed-point functional equation
--   $$H^*_0=\Pi^X_0+\mathbb E\big[\mathbb E[H^*_0\mid\mathcal F_I]\,\big|\,\mathcal F_X\big],\qquad \Pi^X_0=-\mathbb E\big[\mathcal K-\mathbb E[\mathcal K\mid\mathcal F_I]\,\big|\,\mathcal F_X\big],\qquad(7)$$
--   where $\mathcal K=\pi+(\varrho/a)\,dQ/dP$ is the optimal hedging kernel.
--
--   The theorem says that a combined hedge on a claimable risk and a side index is well defined as soon as the two are not functionally dependent in the sense of maximal correlation, and it characterizes the optimal claim on $X$ by a linear fixed-point equation.
--
--   **Formalization Note** Optimality is maximization of $\mathcal U(\pi+[H+G])$ over all feasible pairs ($H$ $\sigma(X)$-measurable, $G$ $\sigma(I)$-measurable, both square-integrable, $\mathbb E_Q[H]=\mathbb E_Q[G]=0$), not merely a solution of the first-order system. Uniqueness is up to $P$-null sets. The paper assumes $a\ge0$; $a>0$ is added because $\mathcal K$ divides by $a$ and problem (4) has no maximizer in general when $a=0$.
-- source:
--   Guiotto & Roncoroni, Combined custom hedging: optimal design, noninsurable exposure, and operational risk management, manuscript OPRE-2019-01-058.R3 (Operations Research 2022), p. 11 (PDF 11), Theorem 1, (6), (7); proof pp. ec24–ec25 (PDF 55–56)

import Mathlib
import Definitions.Def_CustomHedge_Exist_Model

namespace CustomHedge.Exist

open MeasureTheory ProbabilityTheory

variable {Ω EX EY EI : Type*} [MeasurableSpace Ω] [MeasurableSpace EX]
  [MeasurableSpace EY] [MeasurableSpace EI]

/-- Theorem 1 (p. 11). If the maximal correlation of `X` and `I` satisfies `r_XI < 1`,
an optimal combined claim pair `(H*, G*)` of problem (4) exists and is unique (`P`-a.s.),
hence so is the hedge `H* + G*`; and the value-centered optimal claim `H*₀ = H* - E[H*]`
solves the fixed-point equation (7) `H*₀ = Π^X_0 + E[E[H*₀ | 𝓕_I] | 𝓕_X]`. -/
theorem theorem_1 (M : Market Ω EX EY EI) (hS : M.Standing) (hr : M.maxCorr < 1) :
    (∃ H G : Ω → ℝ, M.IsOptimal H G) ∧
      (∀ H₁ G₁ H₂ G₂ : Ω → ℝ, M.IsOptimal H₁ G₁ → M.IsOptimal H₂ G₂ →
        H₁ =ᵐ[M.P] H₂ ∧ G₁ =ᵐ[M.P] G₂ ∧ H₁ + G₁ =ᵐ[M.P] H₂ + G₂) ∧
      (∀ H G : Ω → ℝ, M.IsOptimal H G →
        let H₀ : Ω → ℝ := fun ω => H ω - ∫ ω', H ω' ∂M.P
        H₀ =ᵐ[M.P] M.Pi0X + M.T H₀) := by sorry

end CustomHedge.Exist
