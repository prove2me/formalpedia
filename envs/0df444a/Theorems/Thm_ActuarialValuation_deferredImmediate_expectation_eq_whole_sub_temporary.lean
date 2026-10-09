-- Prove2me | Theorems.Thm_ActuarialValuation_deferredImmediate_expectation_eq_whole_sub_temporary
-- name    : ActuarialValuation.deferredImmediate_expectation_eq_whole_sub_temporary
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T21:35:22.991528+00:00
-- url     : https://prove2.me/theorems/0a0a3a37-be3c-4b4c-8548-37cedc51948c
-- title:
--   Deferred annuity-immediate EPV is whole-life immediate EPV less the temporary immediate EPV
-- statement:
--   For a measurable natural-valued lifetime under the probability measure and discount assumptions stated, the expected present value of a deferred annuity-immediate equals the whole-life annuity-immediate expected present value minus the finite expected present value of its first n possible end-year payments. Whole-life immediate payments start at time one, and deferral moves the first payment to time n plus one.
--
--   **Mathematical statement**
--
--   $$
--   {}_{n|}a_x=a_x-a_{x:\overline n|}
--   $$
-- source:
--   *Life Contingencies*, Chapter 3 §3.3.3 eqs (3.17)–(3.18), using §3.3.2 eqs (3.15)–(3.16), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_curtateSurvivalEvent
import Definitions.Def_actuarial_wholeLifeAnnuityImmediatePV
import Definitions.Def_actuarial_deferredAnnuityImmediatePV
open MeasureTheory

namespace ActuarialValuation

theorem deferredImmediate_expectation_eq_whole_sub_temporary {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v < 1) (n : ℕ)
    :
    (∫ ω, deferredAnnuityImmediatePV K v n ω ∂P) = (∫ ω, wholeLifeAnnuityImmediatePV K v ω ∂P) - (∑ k ∈ Finset.range n, v ^ (k + 1) * (P (curtateSurvivalEvent K (k + 1))).toReal) := by sorry

end ActuarialValuation
