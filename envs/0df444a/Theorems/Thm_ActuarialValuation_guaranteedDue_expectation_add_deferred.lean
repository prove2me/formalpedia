-- Prove2me | Theorems.Thm_ActuarialValuation_guaranteedDue_expectation_add_deferred
-- name    : ActuarialValuation.guaranteedDue_expectation_add_deferred
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T21:44:51.471955+00:00
-- url     : https://prove2.me/theorems/229f9be0-73f5-48da-b0f8-2cf89b08a0b4
-- title:
--   Guaranteed due expectation add deferred
-- statement:
--   States that the expected due guaranteed value is the certain due value plus the expected deferred due value.
--
--   **Mathematical statement**
--
--   $$
--   \mathbb E[Z_{\mathrm{guaranteed,due}}]=Z_{\mathrm{certain,due}}+\mathbb E[Z_{\mathrm{deferred,due}}]
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

theorem guaranteedDue_expectation_add_deferred {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v < 1) (n : ℕ)
    :
    (∫ ω, guaranteedAnnuityDuePV K v n ω ∂P) =
      annuityCertainDuePV v n + ∫ ω, deferredAnnuityDuePV K v n ω ∂P := by sorry

end ActuarialValuation
