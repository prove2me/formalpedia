-- Prove2me | Theorems.Thm_ActuarialValuation_temporaryAnnuityDue_expectation
-- name    : ActuarialValuation.temporaryAnnuityDue_expectation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T20:10:47.282737+00:00
-- url     : https://prove2.me/theorems/d945dc67-e8ed-4534-9c97-80c0bf53910b
-- title:
--   Expected value of an n-year annuity in advance
-- statement:
--   The expected present value of the annuity-due is the sum of each discounted payment multiplied by the probability of survival to its payment time. This gives the present value and expected present value identities in equations 3.15 and 3.16.
--
--   **Mathematical statement**
--
--   $$
--   \mathbb E[Z_{\mathrm{due}}]=\sum_{k=0}^{n-1}v^kP(K\ge k)
--   $$
-- source:
--   *Life Contingencies*, Chapter 3 §3.3.2, equation (3.15), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_temporaryAnnuityDuePV
import Definitions.Def_actuarial_curtateSurvivalEvent
open MeasureTheory

namespace ActuarialValuation

theorem temporaryAnnuityDue_expectation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K) (v : ℝ) (n : ℕ)
    :
    (∫ ω, temporaryAnnuityDuePV K v n ω ∂P) = ∑ k ∈ Finset.range n, v ^ k * (P (curtateSurvivalEvent K k)).toReal := by sorry

end ActuarialValuation
