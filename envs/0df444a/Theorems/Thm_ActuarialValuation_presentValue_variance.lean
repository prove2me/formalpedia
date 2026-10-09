-- Prove2me | Theorems.Thm_ActuarialValuation_presentValue_variance
-- name    : ActuarialValuation.presentValue_variance
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T14:23:48.191889+00:00
-- url     : https://prove2.me/theorems/164f386a-2e3a-4a45-a3ed-03198da828cf
-- title:
--   Variance of finite contingent cashflows
-- statement:
--   The variance of the finite contingent-cashflow present value is the double sum of cashflow weights times the covariance of triggering-event indicators. The result accommodates dependent events and coincident payment times.
--
--   **Mathematical statement**
--
--   $$
--   \operatorname{Var}_P(Z)=\sum_{i\in I}\sum_{j\in I}w_iw_j\bigl(P(A_i\cap A_j)-P(A_i)P(A_j)\bigr)
--   $$
--
--   Here $Z=\sum_{i\in I}w_i\mathbf{1}_{A_i}$, $w_i=d(t_i)c_i$, $I$ is finite, and all $A_i$ are measurable. The terms retain arbitrary dependence between events.
-- source:
--   *Life Contingencies*, Chapter 3, §3.1, equations (3.2)–(3.3) and §3.1.1 (finite-horizon generalisation); https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_presentValue
open MeasureTheory

namespace ActuarialValuation
theorem presentValue_variance {ι Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (payments : Finset ι) (time : ι → ℕ)
    (discount : ℕ → ℝ) (amount : ι → ℝ)
    (trigger : ι → Set Ω)
    (htrigger : ∀ i ∈ payments, MeasurableSet (trigger i)) :
    (ProbabilityTheory.variance
      (presentValue payments time discount amount trigger) P =
      ∑ i ∈ payments, ∑ j ∈ payments,
        (discount (time i) * amount i) *
          (discount (time j) * amount j) *
          ((P (trigger i ∩ trigger j)).toReal -
            (P (trigger i)).toReal * (P (trigger j)).toReal)) := by sorry
end ActuarialValuation
