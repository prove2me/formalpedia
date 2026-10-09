-- Prove2me | Theorems.Thm_ActuarialValuation_wholeLifeDue_zeroInterest_pointwise
-- name    : ActuarialValuation.wholeLifeDue_zeroInterest_pointwise
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T21:46:08.331691+00:00
-- url     : https://prove2.me/theorems/2194de6a-f842-478f-a2b1-ee65a1ea8451
-- title:
--   Whole life due zero interest pointwise
-- statement:
--   States separately that at zero interest the annuity-due present value is K+1 at each outcome.
--
--   **Mathematical statement**
--
--   $$
--   Z_D(v=1)=K+1
--   $$
-- source:
--   Life Contingencies Chapter 3 §3.3.1 equations (3.13)-(3.14), with §3.2.1 (3.7) and derived supporting mathematics; https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_wholeLifeAnnuityDuePV
import Definitions.Def_actuarial_wholeLifeAssurancePV
open MeasureTheory

namespace ActuarialValuation

theorem wholeLifeDue_zeroInterest_pointwise {Ω : Type*} (K : Ω → ℕ) (ω : Ω)
    :
    wholeLifeAnnuityDuePV K 1 ω = (K ω : ℝ) + 1 := by sorry

end ActuarialValuation
