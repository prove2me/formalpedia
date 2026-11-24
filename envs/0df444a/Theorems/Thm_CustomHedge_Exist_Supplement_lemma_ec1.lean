-- Prove2me | Theorems.Thm_CustomHedge_Exist_Supplement_lemma_ec1
-- name    : CustomHedge.Exist.Supplement.lemma_ec1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:39:22.436338+00:00
-- url     : https://prove2.me/theorems/866be436-ba96-4722-a5cf-b3ef5a9d9ee9
-- title:
--   Lemma EC.1, p. ec26 — for Q-centered P ∈ L², U(π + P) − U(π) = (a/2)(E[K₀²] − E[(P₀ + K₀)²])
-- statement:
--   In the combined custom hedging market (standing assumptions: $\pi\in L^2$, $d\mathbb Q/d\mathbb P\in L^2$ positive with $\mathbb P$-mean one, $\varrho\ge0$, $a>0$), let $\mathscr U(Z)=\varrho\mathbb E[Z]-\frac a2\operatorname{Var}[Z]$ and let $\mathcal K_0=\mathcal K-\mathbb E[\mathcal K]$ be the optimal centered hedging kernel, $\mathcal K=\pi+\frac{\varrho}{a}\frac{d\mathbb Q}{d\mathbb P}$.
--
--   Let $P\in L^2(\Omega)$ satisfy $\mathbb E_{\mathbb Q}[P]=0$, and set $P_0=P-\mathbb E[P]$. Then
--   $$\mathscr U(\pi+P)-\mathscr U(\pi)=\frac a2\Big(\mathbb E[\mathcal K_0^2]-\mathbb E\big[(P_0+\mathcal K_0)^2\big]\Big).\qquad(\mathrm{EC.31})$$
--
--   The identity expresses the mean–variance gain of any budget-feasible claim as a distance to $-\mathcal K_0$ in $L^2$; it is the starting point (EC.33) of the proof of Theorem 3.
--
--   Differences from the source:
--   - encoding: $a\ge0$ → $a>0$ (base standing assumptions); reason: $\mathcal K$ divides by $a$; this inherits the base mission's added assumption and excludes the source's $a=0$ case.
-- source:
--   Guiotto & Roncoroni, Combined custom hedging: optimal design, noninsurable exposure, and operational risk management, manuscript OPRE-2019-01-058.R3 (Operations Research 2022), p. ec26 (PDF 57), Lemma EC.1, (EC.31)

import Mathlib
import Definitions.Def_CustomHedge_Exist_Model
import Definitions.Def_CustomHedge_Exist_Supplement_Value

namespace CustomHedge.Exist.Supplement

open MeasureTheory ProbabilityTheory

variable {Ω EX EY EI : Type*} [MeasurableSpace Ω] [MeasurableSpace EX]
  [MeasurableSpace EY] [MeasurableSpace EI]

/-- Lemma EC.1 (p. ec26). For every `P ∈ L²(Ω)` with `E_Q[P] = 0`,
`U(π + P) - U(π) = (a/2) (E[K₀²] - E[(P₀ + K₀)²])`, where `P₀ = P - E[P]` (EC.31). -/
theorem lemma_ec1 (M : Market Ω EX EY EI) (hS : M.Standing) (Pc : Ω → ℝ)
    (hP : MemLp Pc 2 M.P) (hQ : M.EQ Pc = 0) :
    M.U (M.pos + Pc) - M.U M.pos =
      M.a / 2 * (∫ ω, K0 M ω ^ 2 ∂M.P -
        ∫ ω, ((Pc ω - ∫ ω', Pc ω' ∂M.P) + K0 M ω) ^ 2 ∂M.P) := by sorry

end CustomHedge.Exist.Supplement
