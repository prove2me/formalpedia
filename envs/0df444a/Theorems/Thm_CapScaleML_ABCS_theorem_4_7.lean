-- Prove2me | Theorems.Thm_CapScaleML_ABCS_theorem_4_7
-- name    : CapScaleML.ABCS.theorem_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:49:26.605714+00:00
-- url     : https://prove2.me/theorems/fb4900b9-2a72-4db2-8927-1fda05ba5198
-- title:
--   Theorem 4.7 — AP prediction-error bound
-- statement:
--   Let AP receive a predicted arrival rate $\tilde\lambda$ for an instance with actual arrival rate $\lambda$. Its server schedule $\tilde m$ satisfies
--   $$
--   \operatorname{Cost}^{\lambda}(\tilde m,T)\leq
--   \operatorname{Opt}+(\sqrt{2\omega\beta}+\theta)T
--   \|\tilde\lambda-\lambda\|_{\mathrm{MAE}}.
--   $$
--   Consequently, for every $\eta>0$ and $\eta$-accurate prediction, AP's cost is at most $[1+(\sqrt{2\omega\beta}+\theta)\eta]\operatorname{Opt}$. This supplies the optimistic factor used in Theorem 4.11.
--
--   **Formalization Note** The prediction and actual arrivals are integrable. AP is represented by its offline component and integrated online response, and its workload is explicit.
-- source:
--   Rutten & Mukherjee, Online Capacity Scaling Augmented With Unreliable Machine Learning Predictions, arXiv:2101.12160v2, p. 14, Theorem 4.7, (4.8)–(4.9)

import Mathlib
import Definitions.Def_CapScaleML_ABCS_Defs

open MeasureTheory Set
open scoped ENNReal

namespace CapScaleML.ABCS

/-- Theorem 4.7, AP's prediction-error bound and competitive-ratio consequence. -/
theorem theorem_4_7 (ω β θ T : ℝ) (hω : 0 < ω) (hβ : 0 < β)
    (hθ : 0 ≤ θ) (hT : 0 < T) (lam lamHat : ℝ → ℝ)
    (hlam : ∀ t ∈ Icc 0 T, 0 ≤ lam t)
    (hlamHat : ∀ t ∈ Icc 0 T, 0 ≤ lamHat t)
    (hlamI : IntervalIntegrable lam volume 0 T)
    (hlamHatI : IntervalIntegrable lamHat volume 0 T)
    (mAdv qAdv : ℝ → ℝ) (hAP : IsAPAdvice ω β θ T lam lamHat mAdv)
    (hq : IsWorkload T lam mAdv qAdv) :
    cost ω β θ T mAdv qAdv ≤ opt ω β θ T lam +
      ENNReal.ofReal ((Real.sqrt (2 * ω * β) + θ) * (T * mae T lamHat lam)) ∧
    (∀ η : ℝ, 0 < η → IsEtaAccurate ω β θ T η lam lamHat →
      cost ω β θ T mAdv qAdv ≤
        ENNReal.ofReal (1 + (Real.sqrt (2 * ω * β) + θ) * η) * opt ω β θ T lam) := by sorry

end CapScaleML.ABCS
