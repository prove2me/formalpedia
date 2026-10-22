-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_selected_residual_future_joint_of_countwise_factorisation
-- name    : AvramDividend.Classical.chat06_selected_residual_future_joint_of_countwise_factorisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T08:19:03.142687+00:00
-- url     : https://prove2.me/theorems/d53a0ebb-0806-4ca8-bbd9-2cd0f419889b
-- title:
--   Countable gluing of randomly indexed residual survival and complete future events
-- statement:
--   For a measurable random count N, a measurable family of residual waiting times and measurable family of future random elements, assume that on every count-selection event N=n the joint residual-survival/future-event probability is the count-event probability multiplied by common factors c and d. The randomly selected residual and future element then have the claimed joint factor c*d. The proof explicitly constructs measurable disjoint count events and uses countable additivity and ENNReal summation. The exact indexwise renewal factorisation needed in the Poisson construction is supplied separately by the accepted fixed-index residual/future-suffix theorem.
-- source:
--   Source bv_selected_residual_future_joint_countwise_gluing_chat06_20261021.lean, 90 lines, SHA-256 c14f3a64b4c59408a681759f1029d3078e9a6e9a15bcc2bdd08b06e57401e366. Remote private probe 34231cc8-f324-4607-8f08-b9dea142a463 passed source elaboration to deliberate sentinel with zero source errors at pinned Mathlib. Publication and official proof follow separately.

import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.chat06_selected_residual_future_joint_of_countwise_factorisation
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (N : Ω → ℕ) (hN : Measurable N)
    (F : ℕ → Ω → ℝ) (hF : ∀ n, Measurable (F n))
    (G : ℕ → Ω → E) (hG : ∀ n, Measurable (G n))
    (B : Set E) (hB : MeasurableSet B)
    (u : ℝ) (c d : ℝ≥0∞)
    (hFactor : ∀ n : ℕ,
      P {ω | N ω = n ∧ u < F n ω ∧ G n ω ∈ B} =
        (P {ω | N ω = n} * c) * d) :
    P {ω | u < F (N ω) ω ∧ G (N ω) ω ∈ B} = c * d := by sorry
