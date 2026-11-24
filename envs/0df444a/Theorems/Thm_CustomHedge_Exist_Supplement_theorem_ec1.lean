-- Prove2me | Theorems.Thm_CustomHedge_Exist_Supplement_theorem_ec1
-- name    : CustomHedge.Exist.Supplement.theorem_ec1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:40:48.597373+00:00
-- url     : https://prove2.me/theorems/7cbaeb3b-92ef-431d-bc6c-8b19c23a8320
-- title:
--   Theorem EC.1, p. ec12 (corrected: basis index, equation number, uniqueness space, γⁿ) — the Galerkin approximants converge in L² to the solution of the design equation
-- statement:
--   In the combined custom hedging market (standing assumptions as in the base mission, with $a>0$), let $\mathbb H_X=L^2_{X,0}$ be the space of $\mathbb P$-centered finite-variance claims on $X$, $\mathscr I=T$ the operator $T[Z]=\mathbb E[\mathbb E[Z\mid\mathcal F_I]\mid\mathcal F_X]$ and $\Pi^X_0=-\mathbb E[\mathcal K-\mathbb E[\mathcal K\mid\mathcal F_I]\mid\mathcal F_X]$. Assume $r_{XI}<1$ and let $w_1,w_2,\dots$ be a basis of $\mathbb H_X$ (linearly independent with dense span). For $n\ge1$ let $e_1,\dots,e_n$ be an orthonormal basis of $\operatorname{Span}\langle w_1,\dots,w_n\rangle$, $T_n=(T_{kj})$ the matrix with $w_j=\sum_kT_{kj}e_k$, $M_n=(\langle\mathscr I[e_k],e_j\rangle)_{k,j}$ and $\gamma^n=T_n^{-1}(\langle\Pi^X_0,e_j\rangle)_{j}$. Then:
--
--   1. for every $n\ge1$ and every such $e$, $T_n$, the linear system
--   $$T_n^{-1}(\mathbb I_n-M_n)T_n\,h^n=\gamma^n$$
--   has exactly one solution $h^n\in\mathbb R^n$;
--   2. the design equation $H_0=\Pi^X_0+\mathscr I[H_0]$ has a unique solution $H^*_0\in\mathbb H_X$ (up to null sets), and for any choice of $e$, $T_n$ ($n\ge1$) with solutions $h^n$,
--   $$H^*_{0,n}=\sum_{j=1}^nh^n_jw_j\ \longrightarrow\ H^*_0\quad\text{in }L^2.$$
--
--   This is the convergence result for the Galerkin scheme the paper proposes for the design equation, which is used to compute the optimal claim numerically when the integral operator is not compact.
--
--   **Formalization Note** The statement is written for random variables on $\Omega$; under the joint densities of Theorem 2, $w\mapsto w(X)$ maps $L^2_X$ isometrically onto $\sigma(X)$-measurable variables, $\mathscr I[w](X)=T[w(X)]$ (p. ec12) and $\Pi^X_0(X)$ is the term (9) evaluated at $X$ (proof of Theorem 2), so the density form follows. A basis is encoded as a linearly independent sequence with dense linear span, which every Schauder or Hilbert basis is. If $\mathbb H_X$ is finite-dimensional no such sequence exists; the paper's setting (an infinite basis $(w_j)$) excludes that case too.
--
--   Differences from the source:
--   - correction: basis $(w_j)_{j\ge0}$ → basis $w_1,w_2,\dots$ (indexed from 1); reason: only $w_1,\dots,w_n$ enter the spans and the proof (pp. ec38–ec39); with $w_0$ excluded from the spans the limit fails for $H^*_0=w_0$.
--   - correction: "the design equation (9)" → the design equation (8), stated as $H_0=\Pi^X_0+\mathscr I[H_0]$; reason: (9) is the term $\Pi^X_0$; the proof works with (8) ((EC.56)–(EC.57)).
--   - correction: "the unique solution $H^*_0\in L^2_X$" → unique in $L^2_{X,0}=\mathbb H_X$; reason: constants solve the homogeneous equation in $L^2_X$ ($\mathscr I[1]=1$), so uniqueness holds only among centered functions, where the proof (via (5) and ‖T‖ ≤ r_XI) places $H^*_0$.
--   - correction: $\gamma^n=(\langle\Pi^X_0,e_j\rangle)_j$ → $\gamma^n=T_n^{-1}(\langle\Pi^X_0,e_j\rangle)_j$; reason: with the printed $\gamma^n$ the system is not the Galerkin system; the proof's (EC.61)–(EC.62) read $\gamma^n$ as the $w$-coordinates of $\mathscr P_n\Pi^X_0$ and derive $(\mathbb I-M_n)T_nh^n=T_n\gamma^n$, which is the printed system with this $\gamma^n$.
--   - generalization: payoff functions $w_j(x)\in L^2_X$ under the joint densities of Theorem 2, $\mathscr I$ the integral operator (EC.12), $\Pi^X_0$ given by (9) → $\sigma(X)$-measurable random variables, $\mathscr I=T$, $\Pi^X_0=-\mathbb E[\mathcal K-\mathbb E[\mathcal K\mid\mathcal F_I]\mid\mathcal F_X]$, with no density assumption; reason: under the densities these coincide (p. ec12 and the proof of Theorem 2), so the Lean statement specializes to the source's.
--   - generalization: a basis of $L^2_{X,0}$ → a linearly independent sequence with dense finite spans; reason: every Hilbert or Schauder basis meets these conditions, and the proof on p. ec40 uses only convergence of projections onto the nested spans.
--   - reading: "an orthonormal basis $(e_j)$" for each $n$ → the conclusions hold for every choice of orthonormal basis at every level $n\ge1$; reason: the paper fixes an arbitrary such basis.
--   - encoding: $a\ge0$ → $a>0$ (base standing assumptions); reason: $\mathcal K$ divides by $a$; this inherits the base mission's added assumption and excludes the source's $a=0$ case.
-- source:
--   Guiotto & Roncoroni, Combined custom hedging: optimal design, noninsurable exposure, and operational risk management, manuscript OPRE-2019-01-058.R3 (Operations Research 2022), p. ec12 (PDF 43), Theorem EC.1, (EC.12); proof pp. ec38–ec40 (PDF 69–71), EC.3.12, (EC.53)–(EC.62)

import Mathlib
import Definitions.Def_CustomHedge_Exist_Model
import Definitions.Def_CustomHedge_Exist_Supplement_Galerkin

namespace CustomHedge.Exist.Supplement

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω EX EY EI : Type*} [MeasurableSpace Ω] [MeasurableSpace EX]
  [MeasurableSpace EY] [MeasurableSpace EI]

/-- Theorem EC.1 (p. ec12). Let `r_XI < 1` and let `w₁, w₂, …` be a basis of `ℍ_X = L²_{X,0}`.
(i) For every `n ≥ 1`, every orthonormal basis `e₁, …, eₙ` of `Span⟨w₁, …, wₙ⟩` and the
change-of-basis matrix `Tₙ` (`w_j = ∑_k (Tₙ)_{kj} e_k`), the system
`Tₙ⁻¹ (𝕀ₙ - Mₙ) Tₙ hⁿ = γⁿ` has exactly one solution `hⁿ ∈ ℝⁿ`.
(ii) The design equation `H₀ = Π^X_0 + T[H₀]` has a unique solution `H*₀ ∈ ℍ_X`, and for any
such choices of `e`, `Tₙ` (`n ≥ 1`) with solutions `hⁿ`, `∑_{j ≤ n} hⁿ_j w_j → H*₀` in `L²`. -/
theorem theorem_ec1 (M : Market Ω EX EY EI) (hS : M.Standing) (hr : M.maxCorr < 1)
    (w : ℕ → Ω → ℝ) (hw : IsCenteredBasis M w) :
    (∀ n : ℕ, 1 ≤ n → ∀ (e : Fin n → Ω → ℝ) (Tn : Matrix (Fin n) (Fin n) ℝ),
        IsGalerkinFrame M w n e Tn → ∃! h : Fin n → ℝ, GalerkinSystem M e Tn h) ∧
      ∃ H₀ : Ω → ℝ, InCentered M.P M.FX H₀ ∧ H₀ =ᵐ[M.P] M.Pi0X + M.T H₀ ∧
        (∀ H₀' : Ω → ℝ, InCentered M.P M.FX H₀' → H₀' =ᵐ[M.P] M.Pi0X + M.T H₀' →
          H₀' =ᵐ[M.P] H₀) ∧
        ∀ (e : ∀ n : ℕ, Fin n → Ω → ℝ) (Tm : ∀ n : ℕ, Matrix (Fin n) (Fin n) ℝ)
          (h : ∀ n : ℕ, Fin n → ℝ),
          (∀ n : ℕ, 1 ≤ n →
            IsGalerkinFrame M w n (e n) (Tm n) ∧ GalerkinSystem M (e n) (Tm n) (h n)) →
          Tendsto (fun n => l2norm M.P (fun ω => galerkinApprox w (h n) ω - H₀ ω)) atTop
            (𝓝 0) := by sorry

end CustomHedge.Exist.Supplement
