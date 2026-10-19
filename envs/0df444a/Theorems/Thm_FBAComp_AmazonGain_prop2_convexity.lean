-- Prove2me | Theorems.Thm_FBAComp_AmazonGain_prop2_convexity
-- name    : FBAComp.AmazonGain.prop2_convexity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:53:08.371981+00:00
-- url     : https://prove2.me/theorems/8b63054a-40a3-4b2b-82cc-286967206413
-- title:
--   Proof of Proposition 2, p. 38 — convexity of Amazon gain
-- statement:
--   Let $G(\eta)$ be Amazon's fee-optimal FBA equilibrium profit less its no-FBA equilibrium profit. For $\eta_1,\eta_2\in(0,\alpha)$ and $t\in[0,1]$, the gain is convex:
--
--   $$G((1-t)\eta_1+t\eta_2)\leq(1-t)G(\eta_1)+tG(\eta_2).$$
--
--   The statement covers all equilibrium tuples at the three sensitivities, including a change of the active fee constraint. Convexity is the shape condition behind the two thresholds.
--
--   **Formalization Note.** Positive no-FBA seller sales throughout the interval are assumed.
-- source:
--   Lai, Liu, Xiao & Zhao, “Fulfilled by Amazon”, SSRN preprint 3270958 (PDF of 2021-10-08), p. 38, proof of Proposition 2, paragraph beginning “Based on the above”

import Mathlib
import Definitions.Def_FBAComp_AmazonGain_Model

namespace FBAComp.AmazonGain

/-- The combined convexity assertion in the proof of Proposition 2, p. 38:
equilibrium Amazon gain is convex in cross-service sensitivity on `(0, α)`. -/
theorem prop2_convexity (P : Params) (hP : P.Standing) (hI : Interior P) :
    ∀ η₁ ∈ Set.Ioo 0 P.α, ∀ η₂ ∈ Set.Ioo 0 P.α,
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ ηm : ℝ,
      ηm = (1 - t) * η₁ + t * η₂ →
      ∀ wN₁ pAN₁ pSN₁ T₁ wF₁ pAF₁ pSF₁ : ℝ,
      ∀ wN₂ pAN₂ pSN₂ T₂ wF₂ pAF₂ pSF₂ : ℝ,
      ∀ wNm pANm pSNm Tm wFm pAFm pSFm : ℝ,
        IsEqN P η₁ wN₁ pAN₁ pSN₁ →
        IsFeeOptimal P η₁ (profitSN P η₁ pAN₁ pSN₁) T₁ wF₁ pAF₁ pSF₁ →
        IsEqN P η₂ wN₂ pAN₂ pSN₂ →
        IsFeeOptimal P η₂ (profitSN P η₂ pAN₂ pSN₂) T₂ wF₂ pAF₂ pSF₂ →
        IsEqN P ηm wNm pANm pSNm →
        IsFeeOptimal P ηm (profitSN P ηm pANm pSNm) Tm wFm pAFm pSFm →
        gain P ηm wNm pANm pSNm Tm wFm pAFm pSFm ≤
          (1 - t) * gain P η₁ wN₁ pAN₁ pSN₁ T₁ wF₁ pAF₁ pSF₁ +
            t * gain P η₂ wN₂ pAN₂ pSN₂ T₂ wF₂ pAF₂ pSF₂ := by sorry

end FBAComp.AmazonGain
