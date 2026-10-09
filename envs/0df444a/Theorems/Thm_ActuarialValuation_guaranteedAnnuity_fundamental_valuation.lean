-- Prove2me | Theorems.Thm_ActuarialValuation_guaranteedAnnuity_fundamental_valuation
-- name    : ActuarialValuation.guaranteedAnnuity_fundamental_valuation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T22:04:33.733774+00:00
-- url     : https://prove2.me/theorems/366d3214-8176-4c5f-bfaa-8c4e93ecd3d1
-- title:
--   Guaranteed annuity fundamental valuation
-- statement:
--   States a conjunction collecting the due and immediate pathwise decompositions, their survival-probability expectation formulas, and their variance equalities with the deferred annuities.
--
--   **Mathematical statement**
--
--   $$
--   Z_{\mathrm{guaranteed}}=Z_{\mathrm{certain}}+Z_{\mathrm{deferred}}
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

theorem guaranteedAnnuity_fundamental_valuation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v < 1) (n : ℕ)
    :
    (∀ ω, guaranteedAnnuityDuePV K v n ω =
      annuityCertainDuePV v n + deferredAnnuityDuePV K v n ω)
    ∧ (∀ ω, guaranteedAnnuityImmediatePV K v n ω =
      annuityCertainImmediatePV v n + deferredAnnuityImmediatePV K v n ω)
    ∧ ((∫ ω, guaranteedAnnuityDuePV K v n ω ∂P) =
      annuityCertainDuePV v n +
      ∑' k : ℕ, if n ≤ k then v ^ k * (P (curtateSurvivalEvent K k)).toReal else 0)
    ∧ ((∫ ω, guaranteedAnnuityImmediatePV K v n ω ∂P) =
      annuityCertainImmediatePV v n +
      ∑' k : ℕ, if n ≤ k then v ^ (k + 1) * (P (curtateSurvivalEvent K (k + 1))).toReal else 0)
    ∧ (ProbabilityTheory.variance (guaranteedAnnuityDuePV K v n) P =
      ProbabilityTheory.variance (deferredAnnuityDuePV K v n) P)
    ∧ (ProbabilityTheory.variance (guaranteedAnnuityImmediatePV K v n) P =
      ProbabilityTheory.variance (deferredAnnuityImmediatePV K v n) P) := by sorry

end ActuarialValuation
