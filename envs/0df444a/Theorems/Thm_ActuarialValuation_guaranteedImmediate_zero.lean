-- Prove2me | Theorems.Thm_ActuarialValuation_guaranteedImmediate_zero
-- name    : ActuarialValuation.guaranteedImmediate_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T21:38:44.276981+00:00
-- url     : https://prove2.me/theorems/00085382-e09a-4ff1-b638-0a1bd3e86441
-- title:
--   Guaranteed immediate zero
-- statement:
--   States that setting the guarantee term to zero makes the immediate guaranteed annuity equal the whole-life annuity immediate.
--
--   **Mathematical statement**
--
--   $$
--   Z_{\mathrm{guaranteed,immediate}}(n=0)=Z_{\mathrm{whole,immediate}}
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

theorem guaranteedImmediate_zero {Ω : Type*} (K : Ω → ℕ) (v : ℝ) (n : ℕ) (ω : Ω)
    :
    guaranteedAnnuityImmediatePV K v 0 ω = wholeLifeAnnuityImmediatePV K v ω := by sorry

end ActuarialValuation
