-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_selected_past_residual_future_joint_countwise_gluing
-- name    : AvramDividend.Classical.chat06_selected_past_residual_future_joint_countwise_gluing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T08:50:42.137079+00:00
-- url     : https://prove2.me/theorems/7db0ab53-88af-4ea3-b051-1fa95ac16053
-- title:
--   Gluing fixed-count residual and future laws while retaining a measurable past event
-- statement:
--   For a measurable integer-valued random count N, a measurable event H representing an observation of the past, measurable indexed residuals F_n and future observables G_n, suppose the joint survival-and-future event restricted to H and each count cylinder N=n factors as P(H and N=n)*c*d, where c and d do not depend on n. Then the random-selected residual and future event also factors against H: P(H and F_N>u and G_N in B)=P(H)*c*d. The proof partitions H into disjoint count cylinders, uses measurability and countable additivity, and pulls the constant factors through the nonnegative series. Establishing the cylinder hypotheses from the actual observed Poisson past is a further obligation.
-- source:
--   Source bv_selected_past_residual_future_joint_countwise_gluing_chat06_20261021.lean, 77 lines, 2877 bytes, SHA-256 87566f9910fc03e2ab298b5cfba59e28d2f84e3d04af3c021a60b1b682c74d72. Private probe d7da71b2-1623-48ea-925c-477ba66325a7 passed source elaboration to deliberate sentinel with zero candidate errors at pinned revision.

import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.chat06_selected_past_residual_future_joint_countwise_gluing
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (N : Ω → ℕ) (hN : Measurable N)
    (H : Set Ω) (hH : MeasurableSet H)
    (F : ℕ → Ω → ℝ) (hF : ∀ n, Measurable (F n))
    (G : ℕ → Ω → E) (hG : ∀ n, Measurable (G n))
    (B : Set E) (hB : MeasurableSet B)
    (u : ℝ) (c d : ℝ≥0∞)
    (hFactor : ∀ n : ℕ,
      P {ω | ω ∈ H ∧ N ω = n ∧ u < F n ω ∧ G n ω ∈ B} =
        (P {ω | ω ∈ H ∧ N ω = n} * c) * d) :
    P {ω | ω ∈ H ∧ u < F (N ω) ω ∧ G (N ω) ω ∈ B} =
      (P H * c) * d := by sorry
