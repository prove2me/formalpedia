-- Prove2me | Theorems.Thm_ActuarialValuation_deferredImmediate_expectation
-- name    : ActuarialValuation.deferredImmediate_expectation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T21:33:21.043967+00:00
-- url     : https://prove2.me/theorems/793f91fd-6717-4169-8622-d82f3210ce61
-- title:
--   Deferred immediate annuity expected present value
-- statement:
--   The expected deferred immediate present value sums discounted survival probabilities for end-year payments from time n plus one onwards. This is the textbook result in equations (3.17)–(3.18), using the expectation convention in equation (3.3).
--
--   **Mathematical statement**
--
--   $$
--   \mathbb E[Z_{\mathrm{deferred,immediate}}]=\sum_{k=n}^{\infty}v^{k+1}P(K\ge k+1)
--   $$
-- source:
--   *Life Contingencies*, Chapter 3 §3.3.3 eqs (3.17)–(3.18), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_curtateSurvivalEvent
import Definitions.Def_actuarial_deferredAnnuityImmediatePV
open MeasureTheory

namespace ActuarialValuation

theorem deferredImmediate_expectation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v < 1) (n : ℕ)
    :
    (∫ ω, deferredAnnuityImmediatePV K v n ω ∂P) = ∑' k : ℕ, if n ≤ k then v ^ (k + 1) * (P (curtateSurvivalEvent K (k + 1))).toReal else 0 := by sorry

end ActuarialValuation
