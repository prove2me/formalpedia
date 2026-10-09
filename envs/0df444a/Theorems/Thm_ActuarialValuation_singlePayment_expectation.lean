-- Prove2me | Theorems.Thm_ActuarialValuation_singlePayment_expectation
-- name    : ActuarialValuation.singlePayment_expectation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T14:16:12.657792+00:00
-- url     : https://prove2.me/theorems/c67a6f93-6d1b-4add-b748-dd17c1201981
-- title:
--   Single contingent payment: expectation
-- statement:
--   For a single measurable event, the expected discounted cashflow equals the deterministic discounted amount multiplied by the event probability. The underlying measure is a probability measure and all event sets used by the formula are measurable.
--
--   **Mathematical statement**
--
--   $$
--   \mathbb{E}_P[d\,c\,\mathbf{1}_A]=d\,c\,P(A)
--   $$
--
--   Here $d,c\in\mathbb R$, $A$ is measurable, and $P$ is a probability measure.
-- source:
--   *Life Contingencies*, Chapter 3, Equation (3.3), single contingent payment; https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
open MeasureTheory

namespace ActuarialValuation
theorem singlePayment_expectation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (hA : MeasurableSet A) (discount amount : ℝ) :
    (∫ ω, discount * amount * (A.indicator (fun _ : Ω => (1 : ℝ)) ω) ∂P =
      discount * amount * (P A).toReal) := by sorry
end ActuarialValuation
