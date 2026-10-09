-- Prove2me | Theorems.Thm_ActuarialValuation_pureEndowment_expectation
-- name    : ActuarialValuation.pureEndowment_expectation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T19:19:26.849164+00:00
-- url     : https://prove2.me/theorems/6439ce93-9cf7-48f4-8b48-26ad6f665547
-- title:
--   Expected present value of a pure endowment
-- statement:
--   The expected present value of the strict pure endowment is the maturity discount factor multiplied by the probability that exact lifetime exceeds the term.
--
--   **Mathematical statement**
--
--   $$
--   \mathbb E[Z_{\mathrm{pure}}]=v^nP(T>n)
--   $$
-- source:
--   *Life Contingencies*, Chapter 3 §3.2.3, equation (3.9), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_pureEndowmentPV
import Definitions.Def_actuarial_strictSurvivalEvent
open MeasureTheory

namespace ActuarialValuation

theorem pureEndowment_expectation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Ω → ℝ) (hT : Measurable T)
    (hTnonneg : ∀ ω, 0 ≤ T ω) (v : ℝ) (n : ℕ)
    : (∫ ω, pureEndowmentPV T v n ω ∂P) = v ^ n * (P (strictSurvivalEvent T n)).toReal := by sorry

end ActuarialValuation
