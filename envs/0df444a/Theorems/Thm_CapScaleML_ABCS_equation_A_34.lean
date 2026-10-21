-- Prove2me | Theorems.Thm_CapScaleML_ABCS_equation_A_34
-- name    : CapScaleML.ABCS.equation_A_34
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:49:32.744873+00:00
-- url     : https://prove2.me/theorems/e57f666e-c298-4471-890a-3ac0fc03b2be
-- title:
--   Equation (A.34) — online correction cost
-- statement:
--   For AP's online capacity correction $m_2$ responding to the positive underprediction $\Delta\lambda$, its cost is at most
--   $$
--   \operatorname{Cost}^{\Delta\lambda}(m_2,T)
--   \leq(\sqrt{2\omega\beta}+\theta)T\,\|\Delta\lambda\|_{\mathrm{MAE}}.
--   $$
--   The estimate converts missed arrivals into the additive cost paid by AP.
--
--   **Formalization Note** The intermediate Riemann sum in the paper is a proof device; the Lean statement records its outer inequality. Nonnegative integrable arrivals and a workload predicate with an integrable right-hand side are explicit.
-- source:
--   Rutten & Mukherjee, Online Capacity Scaling Augmented With Unreliable Machine Learning Predictions, arXiv:2101.12160v2, p. 35, proof of Theorem 4.7, (A.34)

import Mathlib
import Definitions.Def_CapScaleML_ABCS_Defs

open MeasureTheory Set
open scoped ENNReal

namespace CapScaleML.ABCS

/-- Equation (A.34), the cost of AP's online component. -/
theorem equation_A_34 (ω β θ T : ℝ) (hω : 0 < ω) (hβ : 0 < β)
    (hθ : 0 ≤ θ) (hT : 0 < T) (lam lamHat q₂ : ℝ → ℝ)
    (hlam : ∀ t ∈ Icc 0 T, 0 ≤ lam t)
    (hlamHat : ∀ t ∈ Icc 0 T, 0 ≤ lamHat t)
    (hlamI : IntervalIntegrable lam volume 0 T)
    (hlamHatI : IntervalIntegrable lamHat volume 0 T)
    (hq₂ : IsWorkload T (deltaLam lam lamHat) (apOnline ω β lam lamHat) q₂) :
    cost ω β θ T (apOnline ω β lam lamHat) q₂ ≤
      ENNReal.ofReal ((Real.sqrt (2 * ω * β) + θ) *
        (T * mae T (deltaLam lam lamHat) (fun _ => 0))) := by sorry

end CapScaleML.ABCS
