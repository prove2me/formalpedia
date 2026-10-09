-- Prove2me | Theorems.Thm_ActuarialValuation_guaranteedImmediate_expectation_add_deferred
-- name    : ActuarialValuation.guaranteedImmediate_expectation_add_deferred
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T21:50:41.602296+00:00
-- url     : https://prove2.me/theorems/d2dc0d37-6fdb-423c-9839-c64e5ac7da41
-- title:
--   Guaranteed immediate expectation add deferred
-- statement:
--   States the corresponding expectation decomposition for the immediate guaranteed annuity.
--
--   **Mathematical statement**
--
--   $$
--   \mathbb E[Z_{\mathrm{guaranteed,immediate}}]=Z_{\mathrm{certain,immediate}}+\mathbb E[Z_{\mathrm{deferred,immediate}}]
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

theorem guaranteedImmediate_expectation_add_deferred {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v < 1) (n : ℕ)
    :
    (∫ ω, guaranteedAnnuityImmediatePV K v n ω ∂P) =
      annuityCertainImmediatePV v n + ∫ ω, deferredAnnuityImmediatePV K v n ω ∂P := by sorry

end ActuarialValuation
