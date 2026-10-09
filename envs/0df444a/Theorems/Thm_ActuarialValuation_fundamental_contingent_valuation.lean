-- Prove2me | Theorems.Thm_ActuarialValuation_fundamental_contingent_valuation
-- name    : ActuarialValuation.fundamental_contingent_valuation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T14:24:19.569984+00:00
-- url     : https://prove2.me/theorems/9ee44262-6928-4efb-9ee9-32a76bc4aec0
-- title:
--   Fundamental finite contingent valuation theorem
-- statement:
--   For the same finite collection of contingent payment obligations and probability measure, the expected present value, the second-moment joint-event formula, and the general covariance-based variance formula hold simultaneously. Signed amounts, coincident dates and dependent triggering events are permitted.
--
--   **Mathematical statement**
--
--   $$
--   \mathbb{E}_P[Z]=\sum_{i\in I}w_i P(A_i)
--   $$
--
--   $$
--   \mathbb{E}_P[Z^2]=\sum_{i\in I}\sum_{j\in I}w_iw_j\,P(A_i\cap A_j)
--   $$
--
--   $$
--   \operatorname{Var}_P(Z)=\sum_{i\in I}\sum_{j\in I}w_iw_j\bigl(P(A_i\cap A_j)-P(A_i)P(A_j)\bigr)
--   $$
--
--   Under a probability measure $P$, take a finite set $I$ of payment obligations with measurable events $A_i$, deterministic dates $t_i$, real amounts $c_i$, and discounts $d(t_i)$. Define $w_i=d(t_i)c_i$ and $Z=\sum_{i\in I}w_i\mathbf{1}_{A_i}$. The following three identities hold simultaneously.
-- source:
--   *Life Contingencies*, Chapter 3, §3.1, equations (3.2)–(3.3) and §3.1.1 (finite-horizon generalisation); https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_presentValue
open MeasureTheory

namespace ActuarialValuation
theorem fundamental_contingent_valuation {ι Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (payments : Finset ι) (time : ι → ℕ)
    (discount : ℕ → ℝ) (amount : ι → ℝ)
    (trigger : ι → Set Ω)
    (htrigger : ∀ i ∈ payments, MeasurableSet (trigger i)) :
    (∫ ω, presentValue payments time discount amount trigger ω ∂P =
      ∑ i ∈ payments, discount (time i) * amount i *
        (P (trigger i)).toReal) ∧
    (∫ ω, (presentValue payments time discount amount trigger ω) ^ 2 ∂P =
      ∑ i ∈ payments, ∑ j ∈ payments,
        (discount (time i) * amount i) *
          (discount (time j) * amount j) *
          (P (trigger i ∩ trigger j)).toReal) ∧
    (ProbabilityTheory.variance
      (presentValue payments time discount amount trigger) P =
      ∑ i ∈ payments, ∑ j ∈ payments,
        (discount (time i) * amount i) *
          (discount (time j) * amount j) *
          ((P (trigger i ∩ trigger j)).toReal -
            (P (trigger i)).toReal * (P (trigger j)).toReal)) := by sorry
end ActuarialValuation
