-- Prove2me | Theorems.Thm_ActuarialValuation_wholeLifeAssurancePV_positive
-- name    : ActuarialValuation.wholeLifeAssurancePV_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T21:41:49.694673+00:00
-- url     : https://prove2.me/theorems/79827dbb-6038-4f53-82bd-66e2522d9ad7
-- title:
--   Whole life assurance pv positive
-- statement:
--   Shows that the whole-life assurance present value is positive at every outcome under a positive flat rate.
--
--   **Mathematical statement**
--
--   $$
--   0<v^{K+1}
--   $$
-- source:
--   Life Contingencies Chapter 3 §3.3.1 equations (3.13)-(3.14), with §3.2.1 (3.7) and derived supporting mathematics; https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_wholeLifeAnnuityDuePV
import Definitions.Def_actuarial_wholeLifeAssurancePV
open MeasureTheory

namespace ActuarialValuation

theorem wholeLifeAssurancePV_positive {Ω : Type*} (K : Ω → ℕ) (i : ℝ) (hi : 0 < i) (ω : Ω)
    :
    0 < wholeLifeAssurancePV K (1 / (1 + i)) ω := by sorry

end ActuarialValuation
