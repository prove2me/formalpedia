-- Prove2me | Theorems.Thm_ActuarialValuation_guaranteedImmediate_eq_certain_add_deferred
-- name    : ActuarialValuation.guaranteedImmediate_eq_certain_add_deferred
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T21:32:15.53198+00:00
-- url     : https://prove2.me/theorems/f2341783-d760-47f5-b449-db35ea478aab
-- title:
--   Guaranteed immediate eq certain add deferred
-- statement:
--   States that the immediate guaranteed annuity value splits into the certain immediate value and the deferred immediate value.
--
--   **Mathematical statement**
--
--   $$
--   Z_{\mathrm{guaranteed,immediate}}=Z_{\mathrm{certain,immediate}}+Z_{\mathrm{deferred,immediate}}
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

theorem guaranteedImmediate_eq_certain_add_deferred {Ω : Type*} (K : Ω → ℕ) (v : ℝ) (n : ℕ) (ω : Ω)
    :
    guaranteedAnnuityImmediatePV K v n ω =
      annuityCertainImmediatePV v n + deferredAnnuityImmediatePV K v n ω := by sorry

end ActuarialValuation
