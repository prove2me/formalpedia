-- Prove2me | Theorems.Thm_ActuarialValuation_guaranteedImmediate_expectation_survival_tsum
-- name    : ActuarialValuation.guaranteedImmediate_expectation_survival_tsum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T21:58:08.597544+00:00
-- url     : https://prove2.me/theorems/b51319cb-1421-4123-8645-224d4dbd2061
-- title:
--   Guaranteed immediate expectation survival tsum
-- statement:
--   States the corresponding immediate-annuity expectation formula using curtate survival probabilities and the certain immediate value.
--
--   **Mathematical statement**
--
--   $$
--   \mathbb E[Z_{\mathrm{guaranteed,immediate}}]=\sum_{k=0}^{n-1}v^{k+1}+\sum_{k=n}^{\infty}v^{k+1}P(K\ge k+1)
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

theorem guaranteedImmediate_expectation_survival_tsum {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v < 1) (n : ℕ)
    :
    (∫ ω, guaranteedAnnuityImmediatePV K v n ω ∂P) =
      annuityCertainImmediatePV v n +
      ∑' k : ℕ, if n ≤ k then v ^ (k + 1) * (P (curtateSurvivalEvent K (k + 1))).toReal else 0 := by sorry

end ActuarialValuation
