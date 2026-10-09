-- Prove2me | Theorems.Thm_ActuarialValuation_wholeLifeDue_flatInterest_expectation
-- name    : ActuarialValuation.wholeLifeDue_flatInterest_expectation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T22:01:43.364315+00:00
-- url     : https://prove2.me/theorems/367cf958-dab7-4e19-8f84-f16ede1a673d
-- title:
--   Whole life due flat interest expectation
-- statement:
--   States the EPV relation obtained by integrating the pointwise assurance–annuity identity under a probability measure.
--
--   **Mathematical statement**
--
--   $$
--   \mathbb E[Z_D]=\frac{1+i}{i}(1-\mathbb E[Z_A])
--   $$
-- source:
--   Life Contingencies Chapter 3 §3.3.1 equations (3.13)-(3.14), with §3.2.1 (3.7) and derived supporting mathematics; https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_wholeLifeAnnuityDuePV
import Definitions.Def_actuarial_wholeLifeAssurancePV
open MeasureTheory

namespace ActuarialValuation

theorem wholeLifeDue_flatInterest_expectation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (i : ℝ) (hi : 0 < i)
    :
    (∫ ω, wholeLifeAnnuityDuePV K (1 / (1 + i)) ω ∂P) =
      ((1 + i) / i) *
      (1 - ∫ ω, wholeLifeAssurancePV K (1 / (1 + i)) ω ∂P) := by sorry

end ActuarialValuation
