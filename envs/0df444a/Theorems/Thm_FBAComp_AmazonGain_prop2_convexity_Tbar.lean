-- Prove2me | Theorems.Thm_FBAComp_AmazonGain_prop2_convexity_Tbar
-- name    : FBAComp.AmazonGain.prop2_convexity_Tbar
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:54:11.838997+00:00
-- url     : https://prove2.me/theorems/ee267dba-37d1-4567-97f4-082ba2534250
-- title:
--   Proof of Proposition 2, case (1), p. 38 — gain convex in η when T = T̄
-- statement:
--   Fix the standing parameters $Q_A,Q_S,\alpha,\beta,s_A,s_S,r,c,c_0,g$. For a cross-service sensitivity $\eta\in\mathbb R$, let $\Pi^*_{A,N}(\eta)$ be Amazon's profit at the no-FBA subgame-perfect equilibrium (OEM wholesale price, then simultaneous retail prices), and let $\Pi_{A,F}(\eta;T)$ be Amazon's profit at the FBA subgame outcome after the fee $T$ is fixed. Take the fee equal to the seller's willingness-to-pay threshold
--
--   $$\bar T(\eta)=c+\frac{(1-r)(s_A-s_S)\bigl(8\alpha-(3+r)\alpha\beta^2-6\beta\eta+(2+r)\beta^3\eta\bigr)}{(1-\beta^2)\bigl(8-(3+r)\beta^2\bigr)}.$$
--
--   Then the gain $G_1(\eta)=\Pi_{A,F}(\eta;\bar T(\eta))-\Pi^*_{A,N}(\eta)$ is convex in $\eta$: for all $\eta_1,\eta_2$ and $t\in[0,1]$,
--
--   $$G_1\bigl((1-t)\eta_1+t\eta_2\bigr)\le(1-t)\,G_1(\eta_1)+t\,G_1(\eta_2).$$
--
--   This is the first of the two regimes of the optimal fee $T^*=\min\{\widetilde T,\bar T\}$; together with case (2) it yields the convexity of the equilibrium gain.
--
--   **Formalization Note.** The statement quantifies over all equilibrium tuples at $\eta_1,\eta_2$ and the convex combination, so it does not presuppose the closed forms of Lemmas A.1–A.2. The paper's assumption $\eta\in(0,\alpha)$ is not needed for this case and is not imposed. The added sign conditions $0<s_S$, $0<Q_A,Q_S$ and $0\le c,c_0,g$ are part of the standing assumptions.
-- source:
--   Lai, Liu, Xiao & Zhao, “Fulfilled by Amazon”, SSRN preprint 3270958 (PDF of 2021-10-08), p. 38, proof of Proposition 2, case (1)

import Mathlib
import Definitions.Def_FBAComp_AmazonGain_ClosedForms

namespace FBAComp.AmazonGain

/-- Case (1) of the proof of Proposition 2, p. 38: when the FBA fee is the seller's
threshold `T̄(η)`, Amazon's gain from FBA is a convex function of `η`. -/
theorem prop2_convexity_Tbar (P : Params) (hP : P.Standing) :
    ∀ η₁ η₂ : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ ηm : ℝ,
      ηm = (1 - t) * η₁ + t * η₂ →
      ∀ wN₁ pAN₁ pSN₁ wF₁ pAF₁ pSF₁ : ℝ,
      ∀ wN₂ pAN₂ pSN₂ wF₂ pAF₂ pSF₂ : ℝ,
      ∀ wNm pANm pSNm wFm pAFm pSFm : ℝ,
        IsEqN P η₁ wN₁ pAN₁ pSN₁ →
        IsSubgameEqF P η₁ (Tbar P η₁) wF₁ pAF₁ pSF₁ →
        IsEqN P η₂ wN₂ pAN₂ pSN₂ →
        IsSubgameEqF P η₂ (Tbar P η₂) wF₂ pAF₂ pSF₂ →
        IsEqN P ηm wNm pANm pSNm →
        IsSubgameEqF P ηm (Tbar P ηm) wFm pAFm pSFm →
        gain P ηm wNm pANm pSNm (Tbar P ηm) wFm pAFm pSFm ≤
          (1 - t) * gain P η₁ wN₁ pAN₁ pSN₁ (Tbar P η₁) wF₁ pAF₁ pSF₁ +
            t * gain P η₂ wN₂ pAN₂ pSN₂ (Tbar P η₂) wF₂ pAF₂ pSF₂ := by sorry

end FBAComp.AmazonGain
