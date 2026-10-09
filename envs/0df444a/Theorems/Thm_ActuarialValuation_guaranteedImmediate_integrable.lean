-- Prove2me | Theorems.Thm_ActuarialValuation_guaranteedImmediate_integrable
-- name    : ActuarialValuation.guaranteedImmediate_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T21:41:53.778928+00:00
-- url     : https://prove2.me/theorems/83ca5c5b-43e4-497d-8a49-e4a115a65b0e
-- title:
--   Guaranteed immediate integrable
-- statement:
--   States the corresponding integrability result for the immediate guaranteed present value under the same stated assumptions.
--
--   **Mathematical statement**
--
--   $$
--   0\le v<1\implies Z_{\mathrm{guaranteed,immediate}}\in L^1(P)
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

theorem guaranteedImmediate_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v < 1) (n : ℕ)
    :
    Integrable (guaranteedAnnuityImmediatePV K v n) P := by sorry

end ActuarialValuation
