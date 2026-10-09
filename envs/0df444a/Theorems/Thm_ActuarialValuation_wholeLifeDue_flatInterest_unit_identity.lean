-- Prove2me | Theorems.Thm_ActuarialValuation_wholeLifeDue_flatInterest_unit_identity
-- name    : ActuarialValuation.wholeLifeDue_flatInterest_unit_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T21:45:11.872009+00:00
-- url     : https://prove2.me/theorems/33783fd3-195e-4538-87d8-a30c0f6c1759
-- title:
--   Whole life due flat interest unit identity
-- statement:
--   Rearranges the pointwise relation as a unit identity linking assurance and interest-scaled annuity-due values.
--
--   **Mathematical statement**
--
--   $$
--   Z_A+\frac{i}{1+i}Z_D=1
--   $$
-- source:
--   Life Contingencies Chapter 3 §3.3.1 equations (3.13)-(3.14), with §3.2.1 (3.7) and derived supporting mathematics; https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_wholeLifeAnnuityDuePV
import Definitions.Def_actuarial_wholeLifeAssurancePV
open MeasureTheory

namespace ActuarialValuation

theorem wholeLifeDue_flatInterest_unit_identity {Ω : Type*} (K : Ω → ℕ) (i : ℝ) (hi : 0 < i) (ω : Ω)
    :
    wholeLifeAssurancePV K (1 / (1 + i)) ω +
      (i / (1 + i)) * wholeLifeAnnuityDuePV K (1 / (1 + i)) ω = 1 := by sorry

end ActuarialValuation
