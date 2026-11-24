-- Prove2me | Theorems.Thm_CustomHedge_Exist_Supplement_theorem_3
-- name    : CustomHedge.Exist.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:40:15.454099+00:00
-- url     : https://prove2.me/theorems/8a37706e-2099-4b5a-9b69-33363dcc8bff
-- title:
--   Theorem 3, p. 14 — if r_IX < 1 and ϱ > 0, 𝒞𝒱_{X→X+I} = (a/2ϱ)Var(G*₀ − E[G*₀|F_X]) ≥ (a/2ϱ)(1 − r²_IX)Var(E[K₀ − E[K₀|F_X]|F_I]), tight under independence
-- statement:
--   In the combined custom hedging market (standing assumptions: $\pi\in L^2$, $d\mathbb Q/d\mathbb P\in L^2$ positive with $\mathbb P$-mean one, $\varrho\ge0$, $a>0$), let $r_{IX}$ be the maximal correlation of $I$ and $X$, $\mathcal K_0$ the optimal centered hedging kernel and $\mathcal{CV}_{X\to X+I}=\varrho^{-1}(\mathscr U^*_{\mathcal H_{XI}}-\mathscr U^*_{\mathcal H_X})$ the combination value. Assume $r_{IX}<1$ and $\varrho>0$, and let $(H^*_0,G^*_0)$, with $H^*_0\in\mathbb H_X$ and $G^*_0\in\mathbb H_I$ ($\mathbb P$-centered claims of finite variance on $X$ and on $I$), solve the first-order system (5). Then
--   $$\mathcal{CV}_{X\to X+I}=\frac a{2\varrho}\operatorname{Var}\big(G^*_0-\mathbb E[G^*_0\mid\mathcal F_X]\big)\qquad(12)$$
--   $$\phantom{\mathcal{CV}_{X\to X+I}}\ \ge\frac a{2\varrho}(1-r_{IX}^2)\operatorname{Var}\big(\mathbb E[\mathcal K_0-\mathbb E[\mathcal K_0\mid\mathcal F_X]\mid\mathcal F_I]\big),\qquad(13)$$
--   and the lower bound (13) holds with equality when $X$ and $I$ are independent.
--
--   The identity (12) gives the monetary value of combining a claim on $I$ with a claim on $X$ in terms of the optimal side claim; the bound (13) depends only on $r_{IX}$ and model primitives and is the paper's tool for selecting a side index.
--
--   **Formalization Note** $r_{IX}$ is the maximal correlation with the $\sigma(I)$-measurable variable first (it equals $r_{XI}$). The combination value is the paper's object, built from the suprema of problem (10) over $\mathcal H_X$ and $\mathcal H_X+\mathcal H_I$, not a variance formula.
--
--   Differences from the source:
--   - reading: "pair $(H^*_0(X),G^*_0(I))$ solves system (5)" → $H^*_0\in\mathbb H_X$, $G^*_0\in\mathbb H_I$ satisfying the base `FirstOrder` system a.s.; reason: the paper's $H^*_0,G^*_0$ are the value-centered ($\mathbb P$-centered) claims of Proposition 1.
--   - encoding: Definition 1's indifference amount $m$ → its closed form (11) $\varrho^{-1}(\mathscr U^*_{\mathcal H}-\mathscr U^*_{\mathcal G})$ with $\mathscr U^*$ a supremum; reason: the paper derives (11) from Definition 1 and uses it in the proof (p. ec26); with $\varrho>0$ they agree.
--   - encoding: $a\ge0$ → $a>0$ (base standing assumptions); reason: $\mathcal K$ divides by $a$; this inherits the base mission's added assumption and excludes the source's $a=0$ case.
-- source:
--   Guiotto & Roncoroni, Combined custom hedging: optimal design, noninsurable exposure, and operational risk management, manuscript OPRE-2019-01-058.R3 (Operations Research 2022), p. 14 (PDF 14), Theorem 3, (12), (13); proof pp. ec26–ec28 (PDF 57–59), EC.3.4

import Mathlib
import Definitions.Def_CustomHedge_Exist_Model
import Definitions.Def_CustomHedge_Exist_Supplement_Value

namespace CustomHedge.Exist.Supplement

open MeasureTheory ProbabilityTheory

variable {Ω EX EY EI : Type*} [MeasurableSpace Ω] [MeasurableSpace EX]
  [MeasurableSpace EY] [MeasurableSpace EI]

/-- Theorem 3 (p. 14). Let `r_IX < 1` and `ϱ > 0`, and let `(H*₀, G*₀) ∈ ℍ_X × ℍ_I` solve the
first-order system (5). Then
(12) `𝒞𝒱_{X→X+I} = (a/(2ϱ)) Var(G*₀ - E[G*₀ | 𝓕_X])`,
(13) `(a/(2ϱ)) Var(G*₀ - E[G*₀ | 𝓕_X]) ≥ (a/(2ϱ)) (1 - r_IX²) Var(E[K₀ - E[K₀ | 𝓕_X] | 𝓕_I])`,
and equality holds in (13) when `X` and `I` are independent. -/
theorem theorem_3 (M : Market Ω EX EY EI) (hS : M.Standing)
    (hr : maximalCorrelation M.P M.FI M.FX < 1) (hrho : 0 < M.rho)
    (H₀ G₀ : Ω → ℝ) (hH : InCentered M.P M.FX H₀) (hG : InCentered M.P M.FI G₀)
    (hFO : M.FirstOrder H₀ G₀) :
    CV M = M.a / (2 * M.rho) * variance (G₀ - condExp M.FX M.P G₀) M.P ∧
      M.a / (2 * M.rho) * (1 - maximalCorrelation M.P M.FI M.FX ^ 2) *
          variance (condExp M.FI M.P (K0 M - condExp M.FX M.P (K0 M))) M.P ≤
        M.a / (2 * M.rho) * variance (G₀ - condExp M.FX M.P G₀) M.P ∧
      (IndepFun M.X M.I M.P →
        M.a / (2 * M.rho) * variance (G₀ - condExp M.FX M.P G₀) M.P =
          M.a / (2 * M.rho) * (1 - maximalCorrelation M.P M.FI M.FX ^ 2) *
            variance (condExp M.FI M.P (K0 M - condExp M.FX M.P (K0 M))) M.P) := by sorry

end CustomHedge.Exist.Supplement
