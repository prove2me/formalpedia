-- Prove2me | Theorems.Thm_ActuarialValuation_guaranteedDue_integrable
-- name    : ActuarialValuation.guaranteedDue_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T21:39:38.242651+00:00
-- url     : https://prove2.me/theorems/6de0b9a4-31d1-4ea3-95b4-9dc607c331b0
-- title:
--   Guaranteed due integrable
-- statement:
--   States that the due guaranteed present value is integrable for a probability measure and measurable lifetime when the discount factor is between zero inclusive and one exclusive.
--
--   **Mathematical statement**
--
--   $$
--   0\le v<1\implies Z_{\mathrm{guaranteed,due}}\in L^1(P)
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

theorem guaranteedDue_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v < 1) (n : ℕ)
    :
    Integrable (guaranteedAnnuityDuePV K v n) P := by sorry

end ActuarialValuation
