-- Prove2me | Theorems.Thm_ActuarialValuation_wholeLifeImmediate_expectation
-- name    : ActuarialValuation.wholeLifeImmediate_expectation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T21:31:47.422803+00:00
-- url     : https://prove2.me/theorems/ecfa4ab1-a5f3-4e0e-9c00-ad937afd3234
-- title:
--   Whole-life annuity in arrears expected present value
-- statement:
--   The expected whole-life immediate present value is the infinite sum of end-year discount factors multiplied by the probabilities of survival to those payment dates. This is the textbook result in equations (3.11)–(3.12), using the expectation convention in equation (3.3).
--
--   **Mathematical statement**
--
--   $$
--   \mathbb E[Z_{\mathrm{WL,immediate}}]=\sum_{k=0}^{\infty}v^{k+1}P(K\ge k+1)
--   $$
-- source:
--   *Life Contingencies*, Chapter 3 §3.3.1 eqs (3.11)–(3.12), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_curtateSurvivalEvent
import Definitions.Def_actuarial_wholeLifeAnnuityImmediatePV
open MeasureTheory

namespace ActuarialValuation

theorem wholeLifeImmediate_expectation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v < 1)
    :
    (∫ ω, wholeLifeAnnuityImmediatePV K v ω ∂P) = ∑' k : ℕ, v ^ (k + 1) * (P (curtateSurvivalEvent K (k + 1))).toReal := by sorry

end ActuarialValuation
