-- Prove2me | Theorems.Thm_CapScaleML_ABCS_proposition_6_3
-- name    : CapScaleML.ABCS.proposition_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:49:27.655896+00:00
-- url     : https://prove2.me/theorems/3ec78efe-0039-4408-9c2b-1ba3186f351e
-- title:
--   Proposition 6.3 — ABCS cost compared with advice
-- statement:
--   Let $\tilde m$ be a feasible advised server schedule and $\tilde q$ its workload under the actual arrivals. Any ABCS trajectory $m$ driven by that advice satisfies
--   $$
--   \operatorname{Cost}^{\lambda}(m,T)\leq\mathrm{OCR}\,\operatorname{Cost}^{\lambda}(\tilde m,T).
--   $$
--   OCR is the explicit rate-dependent expression in equation (4.14). This compares the robust controller with the algorithm producing its advice.
--
--   **Formalization Note** The printed preamble says BCS (Algorithm 1), but the proof and use in Theorem 4.11 concern ABCS (Algorithm 3). The statement admits any feasible advice, as the text on p. 24 says. Positive rates and integrability prevent default-valued constants and integrals.
-- source:
--   Rutten & Mukherjee, Online Capacity Scaling Augmented With Unreliable Machine Learning Predictions, arXiv:2101.12160v2, p. 23, Proposition 6.3, (6.10)

import Mathlib
import Definitions.Def_CapScaleML_ABCS_Defs

open MeasureTheory Set
open scoped ENNReal

namespace CapScaleML.ABCS

/-- Proposition 6.3, with the paper's `BCS` typo corrected to `ABCS`. -/
theorem proposition_6_3 (ω β θ T r₁ r₂ R₁ R₂ : ℝ)
    (hω : 0 < ω) (hβ : 0 < β) (hθ : 0 ≤ θ) (hT : 0 < T)
    (hr₁ : 0 < r₁) (hR₁ : r₁ ≤ R₁) (hr₂ : 0 < r₂) (hR₂ : r₂ ≤ R₂)
    (lam : ℝ → ℝ) (hlam : ∀ t ∈ Icc 0 T, 0 ≤ lam t)
    (hlamI : IntervalIntegrable lam volume 0 T)
    (mAdv qAdv : ℝ → ℝ) (hAdv : Admissible T mAdv)
    (hqAdv : IsWorkload T lam mAdv qAdv) (m q : ℝ → ℝ)
    (hm : IsABCS ω β θ T r₁ r₂ R₁ R₂ lam mAdv qAdv m q) :
    cost ω β θ T m q ≤ ENNReal.ofReal (OCR r₁ r₂ R₁ R₂) * cost ω β θ T mAdv qAdv := by sorry

end CapScaleML.ABCS
