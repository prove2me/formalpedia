-- Prove2me | Theorems.Thm_ActuarialValuation_guaranteedDue_zero
-- name    : ActuarialValuation.guaranteedDue_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T21:36:43.655769+00:00
-- url     : https://prove2.me/theorems/5743939a-bfe5-4297-a002-10e5fe5264a1
-- title:
--   Guaranteed due zero
-- statement:
--   States that setting the guarantee term to zero makes the due guaranteed annuity equal the whole-life annuity due.
--
--   **Mathematical statement**
--
--   $$
--   Z_{\mathrm{guaranteed,due}}(n=0)=Z_{\mathrm{whole,due}}
--   $$
-- source:
--   Derived from Life Contingencies §3.3.4, equations (3.19)-(3.20), together with §3.1.1, equations (3.3), (3.5)-(3.6); https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_wholeLifeAnnuityDuePV
import Definitions.Def_actuarial_wholeLifeAnnuityImmediatePV
import Definitions.Def_actuarial_deferredAnnuityDuePV
import Definitions.Def_actuarial_deferredAnnuityImmediatePV
import Definitions.Def_actuarial_curtateSurvivalEvent
import Definitions.Def_actuarial_annuityCertainDuePV
import Definitions.Def_actuarial_annuityCertainImmediatePV
import Definitions.Def_actuarial_guaranteedAnnuityDuePV
import Definitions.Def_actuarial_guaranteedAnnuityImmediatePV
open MeasureTheory

namespace ActuarialValuation

theorem guaranteedDue_zero {Ω : Type*} (K : Ω → ℕ) (v : ℝ) (n : ℕ) (ω : Ω)
    :
    guaranteedAnnuityDuePV K v 0 ω = wholeLifeAnnuityDuePV K v ω := by sorry

end ActuarialValuation
