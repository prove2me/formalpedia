-- Prove2me | Theorems.Thm_FBAComp_AmazonGain_prop2_convexity_Ttilde
-- name    : FBAComp.AmazonGain.prop2_convexity_Ttilde
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T06:53:16.422717+00:00
-- url     : https://prove2.me/theorems/4b120eae-08d0-434b-89fb-b2118cdf4a2a
-- title:
--   Proof of Proposition 2, case (2), p. 38 — gain convex in η when T = T̃
-- statement:
--   Fix the standing parameters. For a cross-service sensitivity $\eta\in\mathbb R$, let $\Pi^*_{A,N}(\eta)$ be Amazon's profit at the no-FBA subgame-perfect equilibrium, and let $\widetilde T(\eta)$ be a fee that maximizes Amazon's profit over all FBA subgame outcomes, **without** the seller's participation constraint; write $\Pi_{A,F}(\eta;\widetilde T(\eta))$ for Amazon's profit there. Then the gain $G_2(\eta)=\Pi_{A,F}(\eta;\widetilde T(\eta))-\Pi^*_{A,N}(\eta)$ is convex in $\eta$: for all $\eta_1,\eta_2$ and $t\in[0,1]$,
--
--   $$G_2\bigl((1-t)\eta_1+t\eta_2\bigr)\le(1-t)\,G_2(\eta_1)+t\,G_2(\eta_2).$$
--
--   This is the second regime of the optimal fee $T^*=\min\{\widetilde T,\bar T\}$ in the proof of Proposition 2.
--
--   **Formalization Note.** $\widetilde T$ is not printed in the paper; it is characterised relationally as Amazon's unconstrained optimal fee. The statement quantifies over all such fees and all equilibrium tuples at the three sensitivities. The restriction $\eta\in(0,\alpha)$ is not needed and not imposed.
-- source:
--   Lai, Liu, Xiao & Zhao, “Fulfilled by Amazon”, SSRN preprint 3270958 (PDF of 2021-10-08), p. 38, proof of Proposition 2, case (2)

import Mathlib
import Definitions.Def_FBAComp_AmazonGain_Model

namespace FBAComp.AmazonGain

/-- Case (2) of the proof of Proposition 2, p. 38: when the FBA fee is Amazon's
unconstrained optimal fee `T̃(η)`, Amazon's gain from FBA is a convex function of `η`. -/
theorem prop2_convexity_Ttilde (P : Params) (hP : P.Standing) :
    ∀ η₁ η₂ : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ ηm : ℝ,
      ηm = (1 - t) * η₁ + t * η₂ →
      ∀ wN₁ pAN₁ pSN₁ T₁ wF₁ pAF₁ pSF₁ : ℝ,
      ∀ wN₂ pAN₂ pSN₂ T₂ wF₂ pAF₂ pSF₂ : ℝ,
      ∀ wNm pANm pSNm Tm wFm pAFm pSFm : ℝ,
        IsEqN P η₁ wN₁ pAN₁ pSN₁ →
        IsUnconstrainedFeeOptimal P η₁ T₁ wF₁ pAF₁ pSF₁ →
        IsEqN P η₂ wN₂ pAN₂ pSN₂ →
        IsUnconstrainedFeeOptimal P η₂ T₂ wF₂ pAF₂ pSF₂ →
        IsEqN P ηm wNm pANm pSNm →
        IsUnconstrainedFeeOptimal P ηm Tm wFm pAFm pSFm →
        gain P ηm wNm pANm pSNm Tm wFm pAFm pSFm ≤
          (1 - t) * gain P η₁ wN₁ pAN₁ pSN₁ T₁ wF₁ pAF₁ pSF₁ +
            t * gain P η₂ wN₂ pAN₂ pSN₂ T₂ wF₂ pAF₂ pSF₂ := by sorry

end FBAComp.AmazonGain
