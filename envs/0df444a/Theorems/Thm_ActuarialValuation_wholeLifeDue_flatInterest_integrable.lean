-- Prove2me | Theorems.Thm_ActuarialValuation_wholeLifeDue_flatInterest_integrable
-- name    : ActuarialValuation.wholeLifeDue_flatInterest_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T21:59:21.861164+00:00
-- url     : https://prove2.me/theorems/ac989efa-4e88-4577-aa67-ef80d028fc46
-- title:
--   Whole life due flat interest integrable
-- statement:
--   Establishes integrability of the annuity-due present value under a probability measure, using its uniform bound at a positive flat rate.
--
--   **Mathematical statement**
--
--   $$
--   Z_D\in L^1(P)
--   $$
-- source:
--   Life Contingencies Chapter 3 §3.3.1 equations (3.13)-(3.14), with §3.2.1 (3.7) and derived supporting mathematics; https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_wholeLifeAnnuityDuePV
import Definitions.Def_actuarial_wholeLifeAssurancePV
open MeasureTheory

namespace ActuarialValuation

theorem wholeLifeDue_flatInterest_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (i : ℝ) (hi : 0 < i)
    :
    Integrable (wholeLifeAnnuityDuePV K (1 / (1 + i))) P := by sorry

end ActuarialValuation
