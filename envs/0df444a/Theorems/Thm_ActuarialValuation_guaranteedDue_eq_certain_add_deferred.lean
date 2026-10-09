-- Prove2me | Theorems.Thm_ActuarialValuation_guaranteedDue_eq_certain_add_deferred
-- name    : ActuarialValuation.guaranteedDue_eq_certain_add_deferred
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T21:31:36.975829+00:00
-- url     : https://prove2.me/theorems/8f939781-78b4-4fa7-a499-4f4116b2502e
-- title:
--   Guaranteed due eq certain add deferred
-- statement:
--   States that the due guaranteed annuity value splits into the certain due value and the deferred due value.
--
--   **Mathematical statement**
--
--   $$
--   Z_{\mathrm{guaranteed,due}}=Z_{\mathrm{certain,due}}+Z_{\mathrm{deferred,due}}
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

theorem guaranteedDue_eq_certain_add_deferred {Ω : Type*} (K : Ω → ℕ) (v : ℝ) (n : ℕ) (ω : Ω)
    :
    guaranteedAnnuityDuePV K v n ω =
      annuityCertainDuePV v n + deferredAnnuityDuePV K v n ω := by sorry

end ActuarialValuation
