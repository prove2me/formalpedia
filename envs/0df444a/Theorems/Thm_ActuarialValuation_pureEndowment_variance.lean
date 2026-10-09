-- Prove2me | Theorems.Thm_ActuarialValuation_pureEndowment_variance
-- name    : ActuarialValuation.pureEndowment_variance
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T19:20:48.934158+00:00
-- url     : https://prove2.me/theorems/d6e4d3b2-417d-45f5-b12c-3b514b84672c
-- title:
--   Variance of a strict pure endowment
-- statement:
--   The strict pure-endowment present value is a discounted indicator of survival strictly beyond the term. Its variance is the squared discount factor times the survival probability and its complement.
--
--   **Mathematical statement**
--
--   $$
--   \operatorname{Var}(Z_{\mathrm{pure}})=v^{2n}P(T>n)(1-P(T>n))
--   $$
-- source:
--   *Life Contingencies*, Chapter 3 §3.2.3, equation (3.9), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_pureEndowmentPV
import Definitions.Def_actuarial_strictSurvivalEvent
open MeasureTheory

namespace ActuarialValuation

theorem pureEndowment_variance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Ω → ℝ) (hT : Measurable T)
    (hTnonneg : ∀ ω, 0 ≤ T ω) (v : ℝ) (n : ℕ)
    : ProbabilityTheory.variance (pureEndowmentPV T v n) P = (v ^ n) ^ 2 * (P (strictSurvivalEvent T n)).toReal * (1 - (P (strictSurvivalEvent T n)).toReal) := by sorry

end ActuarialValuation
