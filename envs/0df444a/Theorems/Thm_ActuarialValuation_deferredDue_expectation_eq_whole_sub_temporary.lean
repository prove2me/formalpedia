-- Prove2me | Theorems.Thm_ActuarialValuation_deferredDue_expectation_eq_whole_sub_temporary
-- name    : ActuarialValuation.deferredDue_expectation_eq_whole_sub_temporary
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T21:33:53.135399+00:00
-- url     : https://prove2.me/theorems/fdbad615-02dc-40b5-93de-87edac808d51
-- title:
--   Deferred annuity-due EPV is whole-life due EPV less the temporary due EPV
-- statement:
--   For a measurable natural-valued lifetime under the probability measure and discount assumptions stated, the expected present value of a deferred annuity-due equals the whole-life annuity-due expected present value minus the finite expected present value of its first n possible payments. The whole-life annuity-due starts at time zero, and deferral moves the first payment to time n.
--
--   **Mathematical statement**
--
--   $$
--   {}_{n|}\ddot a_x=\ddot a_x-\ddot a_{x:\overline n|}
--   $$
-- source:
--   *Life Contingencies*, Chapter 3 §3.3.3 eqs (3.17)–(3.18), using §3.3.2 eqs (3.15)–(3.16), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_curtateSurvivalEvent
import Definitions.Def_actuarial_wholeLifeAnnuityDuePV
import Definitions.Def_actuarial_deferredAnnuityDuePV
open MeasureTheory

namespace ActuarialValuation

theorem deferredDue_expectation_eq_whole_sub_temporary {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v < 1) (n : ℕ)
    :
    (∫ ω, deferredAnnuityDuePV K v n ω ∂P) = (∫ ω, wholeLifeAnnuityDuePV K v ω ∂P) - (∑ k ∈ Finset.range n, v ^ k * (P (curtateSurvivalEvent K k)).toReal) := by sorry

end ActuarialValuation
