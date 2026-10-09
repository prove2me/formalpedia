-- Prove2me | Theorems.Thm_ActuarialValuation_wholeLifeAssurance_flatInterest_integrable
-- name    : ActuarialValuation.wholeLifeAssurance_flatInterest_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T22:00:49.908602+00:00
-- url     : https://prove2.me/theorems/1747012d-61b8-463e-a07b-67cdec324f04
-- title:
--   Whole life assurance flat interest integrable
-- statement:
--   Establishes integrability of the assurance present value under a probability measure at a positive flat rate.
--
--   **Mathematical statement**
--
--   $$
--   Z_A\in L^1(P)
--   $$
-- source:
--   Life Contingencies Chapter 3 §3.3.1 equations (3.13)-(3.14), with §3.2.1 (3.7) and derived supporting mathematics; https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_wholeLifeAnnuityDuePV
import Definitions.Def_actuarial_wholeLifeAssurancePV
open MeasureTheory

namespace ActuarialValuation

theorem wholeLifeAssurance_flatInterest_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (i : ℝ) (hi : 0 < i)
    :
    Integrable (wholeLifeAssurancePV K (1 / (1 + i))) P := by sorry

end ActuarialValuation
