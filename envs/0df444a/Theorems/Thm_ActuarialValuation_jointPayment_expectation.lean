-- Prove2me | Theorems.Thm_ActuarialValuation_jointPayment_expectation
-- name    : ActuarialValuation.jointPayment_expectation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T14:16:55.820024+00:00
-- url     : https://prove2.me/theorems/62212817-bc0c-429b-8317-97f9b9e7556e
-- title:
--   Joint-event indicator expectation
-- statement:
--   The expectation of the product of two event indicators equals the probability of their intersection, including for dependent events. The underlying measure is a probability measure and all event sets used by the formula are measurable.
--
--   **Mathematical statement**
--
--   $$
--   \mathbb{E}_P[\mathbf{1}_A\mathbf{1}_B]=P(A\cap B)
--   $$
--
--   Here $A,B$ are measurable events and $P$ is a probability measure; no independence is assumed.
-- source:
--   *Life Contingencies*, Chapter 3, §3.1.1, two event indicators; https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
open MeasureTheory

namespace ActuarialValuation
theorem jointPayment_expectation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A B : Set Ω) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (∫ ω, (A.indicator (fun _ : Ω => (1 : ℝ)) ω) *
      (B.indicator (fun _ : Ω => (1 : ℝ)) ω) ∂P =
      (P (A ∩ B)).toReal) := by sorry
end ActuarialValuation
