-- Prove2me | Theorems.Thm_ActuarialValuation_wholeLifeImmediate_eq_due_sub_one
-- name    : ActuarialValuation.wholeLifeImmediate_eq_due_sub_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T21:21:34.851333+00:00
-- url     : https://prove2.me/theorems/b447efb7-b2fc-48a9-bdf2-58855e4a5f02
-- title:
--   Whole-life immediate PV is due PV minus its first payment
-- statement:
--   For each realised lifetime, the whole-life immediate present value is the due present value less the certain unit payment at time zero. This is the pathwise relation between the textbook results in equations (3.11)–(3.12).
--
--   **Mathematical statement**
--
--   $$
--   Z_{\mathrm{WL,immediate}}=Z_{\mathrm{WL,due}}-1
--   $$
-- source:
--   *Life Contingencies*, Chapter 3 §3.3.1 eqs (3.11)–(3.12), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_curtateSurvivalEvent
import Definitions.Def_actuarial_wholeLifeAnnuityDuePV
import Definitions.Def_actuarial_wholeLifeAnnuityImmediatePV
open MeasureTheory

namespace ActuarialValuation

theorem wholeLifeImmediate_eq_due_sub_one {Ω : Type*} (K : Ω → ℕ) (v : ℝ) (ω : Ω)
    :
    wholeLifeAnnuityImmediatePV K v ω = wholeLifeAnnuityDuePV K v ω - 1 := by sorry

end ActuarialValuation
