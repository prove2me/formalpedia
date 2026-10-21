-- Prove2me | Theorems.Thm_CapScaleML_ABCS_proposition_6_1
-- name    : CapScaleML.ABCS.proposition_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:49:28.753352+00:00
-- url     : https://prove2.me/theorems/37483b4b-214e-4e20-a369-59d2bbfd32b6
-- title:
--   Proposition 6.1 — pessimistic bound for ABCS
-- statement:
--   For any finite-horizon instance with nonnegative arrival rate and any ABCS trajectory $m$ driven by advice, its total cost obeys
--   $$
--   \operatorname{Cost}^{\lambda}(m,T)\leq\mathrm{PCR}\operatorname{Opt}.
--   $$
--   Here PCR is the explicit expression in equation (4.14), depending only on the four response rates. The bound gives the prediction-independent half of Theorem 4.11.
--
--   **Formalization Note** The Lean statement allows any feasible advice $\tilde m$ (with $\tilde m(0)=0$, nonnegative and integrable) together with its workload $\tilde q$ under the actual arrivals, not only AP's; AP's advice is such a schedule, and the paper notes that ABCS is oblivious to the source of the advice (Remark 4.10, p. 15) while the appendix argument uses only the two possible values of each switching coefficient. It requires integrability and positive $r_1,r_2$ so the displayed constants retain their intended values.
-- source:
--   Rutten & Mukherjee, Online Capacity Scaling Augmented With Unreliable Machine Learning Predictions, arXiv:2101.12160v2, p. 22, Proposition 6.1, (6.1)

import Mathlib
import Definitions.Def_CapScaleML_ABCS_Defs

open MeasureTheory Set
open scoped ENNReal

namespace CapScaleML.ABCS

/-- Proposition 6.1: the pessimistic competitive-ratio bound. -/
theorem proposition_6_1 (ω β θ T r₁ r₂ R₁ R₂ : ℝ)
    (hω : 0 < ω) (hβ : 0 < β) (hθ : 0 ≤ θ) (hT : 0 < T)
    (hr₁ : 0 < r₁) (hR₁ : r₁ ≤ R₁) (hr₂ : 0 < r₂) (hR₂ : r₂ ≤ R₂)
    (lam : ℝ → ℝ) (hlam : ∀ t ∈ Icc 0 T, 0 ≤ lam t)
    (hlamI : IntervalIntegrable lam volume 0 T)
    (mAdv qAdv : ℝ → ℝ) (hAdv : Admissible T mAdv)
    (hqAdv : IsWorkload T lam mAdv qAdv) (m q : ℝ → ℝ)
    (hm : IsABCS ω β θ T r₁ r₂ R₁ R₂ lam mAdv qAdv m q) :
    cost ω β θ T m q ≤ ENNReal.ofReal (PCR r₁ r₂ R₁ R₂) * opt ω β θ T lam := by sorry

end CapScaleML.ABCS
