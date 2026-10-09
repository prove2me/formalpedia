-- Prove2me | Theorems.Thm_ActuarialValuation_temporaryAnnuityImmediate_expectation
-- name    : ActuarialValuation.temporaryAnnuityImmediate_expectation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T20:12:06.26902+00:00
-- url     : https://prove2.me/theorems/7c01e3bd-f399-4fa6-b725-cc0b4a4d932b
-- title:
--   Expected value of an n-year annuity in arrears
-- statement:
--   The expected present value of the annuity-immediate is the sum of each discounted end-year payment multiplied by the probability of survival to that payment date. This gives the present value and expected present value identities in equations 3.15 and 3.16.
--
--   **Mathematical statement**
--
--   $$
--   \mathbb E[Z_{\mathrm{immediate}}]=\sum_{k=0}^{n-1}v^{k+1}P(K\ge k+1)
--   $$
-- source:
--   *Life Contingencies*, Chapter 3 §3.3.2, equation (3.16), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_temporaryAnnuityImmediatePV
import Definitions.Def_actuarial_curtateSurvivalEvent
open MeasureTheory

namespace ActuarialValuation

theorem temporaryAnnuityImmediate_expectation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K) (v : ℝ) (n : ℕ)
    :
    (∫ ω, temporaryAnnuityImmediatePV K v n ω ∂P) = ∑ k ∈ Finset.range n, v ^ (k + 1) * (P (curtateSurvivalEvent K (k + 1))).toReal := by sorry

end ActuarialValuation
