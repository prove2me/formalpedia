-- Prove2me | Theorems.Thm_ActuarialValuation_wholeLifeDue_flatInterest_pointwise
-- name    : ActuarialValuation.wholeLifeDue_flatInterest_pointwise
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T21:44:13.102836+00:00
-- url     : https://prove2.me/theorems/b8c62b1b-c060-44c4-9673-b28226d84c39
-- title:
--   Whole life due flat interest pointwise
-- statement:
--   Gives the pointwise relation between the annuity-due present value and assurance present value, obtained from the finite geometric sum.
--
--   **Mathematical statement**
--
--   $$
--   Z_D=\frac{1+i}{i}(1-Z_A)
--   $$
-- source:
--   Life Contingencies Chapter 3 §3.3.1 equations (3.13)-(3.14), with §3.2.1 (3.7) and derived supporting mathematics; https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_wholeLifeAnnuityDuePV
import Definitions.Def_actuarial_wholeLifeAssurancePV
open MeasureTheory

namespace ActuarialValuation

theorem wholeLifeDue_flatInterest_pointwise {Ω : Type*} (K : Ω → ℕ) (i : ℝ) (hi : 0 < i) (ω : Ω)
    :
    wholeLifeAnnuityDuePV K (1 / (1 + i)) ω =
      ((1 + i) / i) * (1 - wholeLifeAssurancePV K (1 / (1 + i)) ω) := by sorry

end ActuarialValuation
