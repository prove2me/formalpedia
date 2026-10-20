-- Prove2me | Theorems.Thm_FBAComp_AmazonGain_prop2_eta_zero
-- name    : FBAComp.AmazonGain.prop2_eta_zero
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-10-19T06:53:21.619388+00:00
-- url     : https://prove2.me/theorems/7979e28c-3529-46ef-8eb0-506efcb8ce3a
-- title:
--   Proof of Proposition 2, p. 38 — positive gain at zero
-- statement:
--   At zero cross-service sensitivity, Amazon's equilibrium gain from offering FBA is strictly positive:
--
--   $$\Pi_{A,F}^*(0)-\Pi_{A,N}^*(0)>0.$$
--
--   This supplies a positive value at the low-sensitivity edge of the threshold claim.
--
--   **Formalization Note.** The game is defined at $\eta=0$ although its economic domain is $(0,\alpha)$. The printed proof uses $T^*>c$, which need not hold; only its conclusion is asserted.
-- source:
--   Lai, Liu, Xiao & Zhao, “Fulfilled by Amazon”, SSRN preprint 3270958 (PDF of 2021-10-08), p. 38, proof of Proposition 2, paragraph beginning “Next we prove”

import Mathlib
import Definitions.Def_FBAComp_AmazonGain_Model

namespace FBAComp.AmazonGain

/-- The positive-gain assertion at `η = 0` in the proof of Proposition 2, p. 38. -/
theorem prop2_eta_zero (P : Params) (hP : P.Standing) (hI : Interior P)
    (wN pAN pSN T wF pAF pSF : ℝ)
    (hN : IsEqN P 0 wN pAN pSN)
    (hF : IsFeeOptimal P 0 (profitSN P 0 pAN pSN) T wF pAF pSF) :
    0 < gain P 0 wN pAN pSN T wF pAF pSF := by sorry

end FBAComp.AmazonGain
