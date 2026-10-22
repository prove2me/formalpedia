-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_iid_random_count_observed_count_event_residual_future_joint
-- name    : AvramDividend.Classical.chat06_iid_random_count_observed_count_event_residual_future_joint
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T11:23:21.76326+00:00
-- url     : https://prove2.me/theorems/509308a0-d561-4c7d-b112-f03c96afb5e1
-- title:
--   Joint residual and whole-future waiting-time law independent of every event of the current Poisson count
-- statement:
--   Let N be a measurable renewal count at a fixed clock, whose count selection events agree almost surely with the corresponding finite arrival intervals for iid Exp(1) waiting times. Suppose the complete post-next-arrival suffix at every deterministic index has the same law mu. For every measurable subset C of integer counts, every nonnegative residual threshold t, and every measurable whole-future suffix event B, the probability of N in C, residual>t and future in B factors as P(N in C)*exp(-t)*mu(B). This is independence of the selected residual and entire future waiting-time suffix from the observed count N under the stated construction hypotheses. Independence from all the earlier arrival times and the full natural filtration remains a further obligation.
-- source:
--   Source bv_iid_random_count_observed_count_event_residual_future_joint_v2_chat06_20261021.lean, 93 lines, 4022 bytes, SHA-256 f344f022f938f5abad73d16f90dfe67b90f461f78bf37bada6fb181a92191379. Private probe 3ee77eef-d299-4b1a-ac6b-1b9890db6760 passed source elaboration to sentinel with zero source errors. Initial version failed at set membership of H and its comprehension, corrected via Set.mem_setOf_eq.

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Exp
import Theorems.Thm_AvramDividend_Classical_chat06_indexed_count_event_residual_future_joint
import Theorems.Thm_AvramDividend_Classical_chat06_selected_past_residual_future_joint_countwise_gluing

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.chat06_iid_random_count_observed_count_event_residual_future_joint
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P)
    (N : Ω → ℕ) (hN : Measurable N)
    (clock t : ℝ) (ht : 0 ≤ t)
    (μ : Measure (ℕ → ℝ))
    (hLaw : ∀ n,
      HasLaw (fun ω (j : ℕ) => τ (n + 1 + j) ω) μ P)
    (C : Set ℕ) (hC : MeasurableSet C)
    (B : Set (ℕ → ℝ)) (hB : MeasurableSet B)
    (hTail : ∀ n (u : ℝ), 0 ≤ u →
      P {ω | u < τ n ω} = ENNReal.ofReal (Real.exp (-u)))
    (hCount : ∀ n : ℕ,
      (fun ω : Ω => N ω = n) =ᵐ[P]
        (fun ω => (∑ i ∈ Finset.range n, τ i ω) ≤ clock ∧
          clock < ∑ i ∈ Finset.range (n + 1), τ i ω)) :
    P {ω | N ω ∈ C ∧
      t < τ (N ω) ω - (clock - ∑ i ∈ Finset.range (N ω), τ i ω) ∧
      (fun j : ℕ => τ (N ω + 1 + j) ω) ∈ B} =
        (P {ω | N ω ∈ C} *
          ENNReal.ofReal (Real.exp (-t))) * μ B := by sorry
