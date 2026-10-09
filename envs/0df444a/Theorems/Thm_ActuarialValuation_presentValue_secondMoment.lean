-- Prove2me | Theorems.Thm_ActuarialValuation_presentValue_secondMoment
-- name    : ActuarialValuation.presentValue_secondMoment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T14:21:19.906411+00:00
-- url     : https://prove2.me/theorems/94a3b6a5-f0ea-47ba-bcea-9e5927d84216
-- title:
--   Second moment of finite contingent cashflows
-- statement:
--   The second moment of finite event-contingent cashflows is a double sum over ordered pairs of distinct or identical obligation indices, weighted by joint-event probabilities. No independence hypothesis is imposed.
--
--   **Mathematical statement**
--
--   $$
--   \mathbb{E}_P[Z^2]=\sum_{i\in I}\sum_{j\in I}w_iw_j\,P(A_i\cap A_j)
--   $$
--
--   Here $Z=\sum_{i\in I}w_i\mathbf{1}_{A_i}$, $w_i=d(t_i)c_i$, $I$ is finite, and all $A_i$ are measurable. The formula includes diagonal terms and both orders of every off-diagonal pair.
-- source:
--   *Life Contingencies*, Chapter 3, §3.1, equations (3.2)–(3.3) and §3.1.1 (finite-horizon generalisation); https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_presentValue
open MeasureTheory

namespace ActuarialValuation
theorem presentValue_secondMoment {ι Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (payments : Finset ι) (time : ι → ℕ)
    (discount : ℕ → ℝ) (amount : ι → ℝ)
    (trigger : ι → Set Ω)
    (htrigger : ∀ i ∈ payments, MeasurableSet (trigger i)) :
    (∫ ω, (presentValue payments time discount amount trigger ω) ^ 2 ∂P =
      ∑ i ∈ payments, ∑ j ∈ payments,
        (discount (time i) * amount i) *
          (discount (time j) * amount j) *
          (P (trigger i ∩ trigger j)).toReal) := by sorry
end ActuarialValuation
