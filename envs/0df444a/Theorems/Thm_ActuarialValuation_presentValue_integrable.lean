-- Prove2me | Theorems.Thm_ActuarialValuation_presentValue_integrable
-- name    : ActuarialValuation.presentValue_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T14:14:58.969925+00:00
-- url     : https://prove2.me/theorems/7b13f6ba-ce75-424b-97cc-21bece9294fc
-- title:
--   Finite contingent present value is integrable
-- statement:
--   The present value of a finite set of distinct payment obligations is integrable for any probability measure, provided the payment-triggering events are measurable. Each obligation has its own amount, trigger and date; multiple obligations may share a date.
--
--   **Mathematical statement**
--
--   $$
--   Z\in L^1(P)
--   $$
--
--   Here $Z$ is the finite present value defined in the mission, $P$ is a probability measure, and every scheduled trigger event is measurable.
-- source:
--   *Life Contingencies*, Chapter 3, §3.1, equations (3.2)–(3.3) and §3.1.1 (finite-horizon generalisation); https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_presentValue
open MeasureTheory

namespace ActuarialValuation
theorem presentValue_integrable {ι Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (payments : Finset ι) (time : ι → ℕ)
    (discount : ℕ → ℝ) (amount : ι → ℝ)
    (trigger : ι → Set Ω)
    (htrigger : ∀ i ∈ payments, MeasurableSet (trigger i)) :
    Integrable (presentValue payments time discount amount trigger) P := by sorry
end ActuarialValuation
