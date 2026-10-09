-- Prove2me | Theorems.Thm_ActuarialValuation_guaranteedDue_expectation_survival_tsum
-- name    : ActuarialValuation.guaranteedDue_expectation_survival_tsum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T21:57:17.326216+00:00
-- url     : https://prove2.me/theorems/a54618a8-5107-4b3f-b66c-df67d0113483
-- title:
--   Guaranteed due expectation survival tsum
-- statement:
--   States a due-annuity expectation formula using probabilities of the relevant curtate survival events, with the certain due value included.
--
--   **Mathematical statement**
--
--   $$
--   \mathbb E[Z_{\mathrm{guaranteed,due}}]=\sum_{k=0}^{n-1}v^k+\sum_{k=n}^{\infty}v^kP(K\ge k)
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

theorem guaranteedDue_expectation_survival_tsum {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v < 1) (n : ℕ)
    :
    (∫ ω, guaranteedAnnuityDuePV K v n ω ∂P) =
      annuityCertainDuePV v n +
      ∑' k : ℕ, if n ≤ k then v ^ k * (P (curtateSurvivalEvent K k)).toReal else 0 := by sorry

end ActuarialValuation
