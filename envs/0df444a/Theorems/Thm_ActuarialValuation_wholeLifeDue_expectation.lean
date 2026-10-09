-- Prove2me | Theorems.Thm_ActuarialValuation_wholeLifeDue_expectation
-- name    : ActuarialValuation.wholeLifeDue_expectation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T21:31:18.507531+00:00
-- url     : https://prove2.me/theorems/7be4645e-8ef9-4f78-8f70-fb4d8cc347aa
-- title:
--   Whole-life annuity in advance expected present value
-- statement:
--   The expected whole-life due present value is the infinite sum of discounted probabilities of survival to each beginning-of-year payment date, including time zero. This is the textbook result in equations (3.11)–(3.12), using the expectation convention in equation (3.3).
--
--   **Mathematical statement**
--
--   $$
--   \mathbb E[Z_{\mathrm{WL,due}}]=\sum_{k=0}^{\infty}v^kP(K\ge k)
--   $$
-- source:
--   *Life Contingencies*, Chapter 3 §3.3.1 eqs (3.11)–(3.12), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_curtateSurvivalEvent
import Definitions.Def_actuarial_wholeLifeAnnuityDuePV
open MeasureTheory

namespace ActuarialValuation

theorem wholeLifeDue_expectation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v < 1)
    :
    (∫ ω, wholeLifeAnnuityDuePV K v ω ∂P) = ∑' k : ℕ, v ^ k * (P (curtateSurvivalEvent K k)).toReal := by sorry

end ActuarialValuation
