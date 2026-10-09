-- Prove2me | Theorems.Thm_ActuarialValuation_presentValue_expectation
-- name    : ActuarialValuation.presentValue_expectation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T14:16:40.676756+00:00
-- url     : https://prove2.me/theorems/dbb4433e-dca6-447c-a86b-f2e422729399
-- title:
--   Expected present value of finite contingent cashflows
-- statement:
--   The expected present value of a finite set of distinct contingent payments equals the sum of each payment's discounted amount times the probability of its triggering event. Different payments may have the same date and their triggering events may be arbitrarily dependent.
--
--   **Mathematical statement**
--
--   $$
--   \mathbb{E}_P[Z]=\sum_{i\in I}w_i P(A_i)
--   $$
--
--   Here $Z=\sum_{i\in I}w_i\mathbf{1}_{A_i}$, $w_i=d(t_i)c_i$, $I$ is finite, and all $A_i$ are measurable.
-- source:
--   *Life Contingencies*, Chapter 3, §3.1, equations (3.2)–(3.3) and §3.1.1 (finite-horizon generalisation); https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_presentValue
open MeasureTheory

namespace ActuarialValuation
theorem presentValue_expectation {ι Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (payments : Finset ι) (time : ι → ℕ)
    (discount : ℕ → ℝ) (amount : ι → ℝ)
    (trigger : ι → Set Ω)
    (htrigger : ∀ i ∈ payments, MeasurableSet (trigger i)) :
    (∫ ω, presentValue payments time discount amount trigger ω ∂P =
      ∑ i ∈ payments, discount (time i) * amount i *
        (P (trigger i)).toReal) := by sorry
end ActuarialValuation
