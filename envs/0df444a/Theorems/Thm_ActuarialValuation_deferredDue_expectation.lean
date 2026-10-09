-- Prove2me | Theorems.Thm_ActuarialValuation_deferredDue_expectation
-- name    : ActuarialValuation.deferredDue_expectation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T21:32:27.597093+00:00
-- url     : https://prove2.me/theorems/e2ee4200-9667-472c-82b6-fd5c407d0845
-- title:
--   Deferred due annuity expected present value
-- statement:
--   The expected deferred due present value sums discounted survival probabilities for beginning-of-year payments from time n onwards. This is the textbook result in equations (3.17)–(3.18), using the expectation convention in equation (3.3).
--
--   **Mathematical statement**
--
--   $$
--   \mathbb E[Z_{\mathrm{deferred,due}}]=\sum_{k=n}^{\infty}v^kP(K\ge k)
--   $$
-- source:
--   *Life Contingencies*, Chapter 3 §3.3.3 eqs (3.17)–(3.18), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_curtateSurvivalEvent
import Definitions.Def_actuarial_deferredAnnuityDuePV
open MeasureTheory

namespace ActuarialValuation

theorem deferredDue_expectation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v < 1) (n : ℕ)
    :
    (∫ ω, deferredAnnuityDuePV K v n ω ∂P) = ∑' k : ℕ, if n ≤ k then v ^ k * (P (curtateSurvivalEvent K k)).toReal else 0 := by sorry

end ActuarialValuation
