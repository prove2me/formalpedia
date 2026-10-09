-- Prove2me | Theorems.Thm_ActuarialValuation_guaranteedDue_variance_eq_deferred
-- name    : ActuarialValuation.guaranteedDue_variance_eq_deferred
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T22:00:27.059705+00:00
-- url     : https://prove2.me/theorems/f02cd10a-2c76-4305-a478-1108eae3fc86
-- title:
--   Guaranteed due variance eq deferred
-- statement:
--   States that the due guaranteed annuity and deferred due annuity have equal variance under the stated assumptions, since adding a deterministic certain value does not change variance.
--
--   **Mathematical statement**
--
--   $$
--   \operatorname{Var}(Z_{\mathrm{guaranteed,due}})=\operatorname{Var}(Z_{\mathrm{deferred,due}})
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

theorem guaranteedDue_variance_eq_deferred {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v < 1) (n : ℕ)
    :
    ProbabilityTheory.variance (guaranteedAnnuityDuePV K v n) P =
      ProbabilityTheory.variance (deferredAnnuityDuePV K v n) P := by sorry

end ActuarialValuation
