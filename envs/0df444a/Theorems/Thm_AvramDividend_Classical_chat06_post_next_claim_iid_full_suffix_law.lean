-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_post_next_claim_iid_full_suffix_law
-- name    : AvramDividend.Classical.chat06_post_next_claim_iid_full_suffix_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T16:25:31.439014+00:00
-- url     : https://prove2.me/theorems/21bae24d-9597-4971-88be-0d64bbb80824
-- title:
--   Complete iid waiting-time law of the suffix after the next claim
-- statement:
--   Given independent waiting times, identical laws of all deterministic future suffixes, and the observable-past cylinder characterisation of each selected claim index, the complete infinite-dimensional waiting-time sequence strictly after the selected next claim has the same joint law. This proves the stopped suffix law but not the memoryless residual waiting time from the observation time to the next claim.
-- source:
--   Chat 06 original Lean construction from accepted finite-past and whole-future independent results, pinned Prove2Me Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Theorems.Thm_AvramDividend_Classical_chat06_stopped_future_full_joint_law_ae_selection
import Theorems.Thm_AvramDividend_Classical_chat06_masked_iid_prefix_full_suffix_independence
import Theorems.Thm_AvramDividend_Classical_chat06_all_count_events_past_cylinders

open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem AvramDividend.Classical.chat06_post_next_claim_iid_full_suffix_law
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P)
    (N : Ω → ℕ) (hN : Measurable N)
    (μ : Measure (ℕ → ℝ))
    (hLaw : ∀ n : ℕ,
      HasLaw (fun ω (j : ℕ) => τ (n + 1 + j) ω) μ P)
    (hZero : ∃ S : Set (ℕ → ℝ), MeasurableSet S ∧
      (fun ω : Ω => N ω = 0) =ᵐ[P]
      (fun ω : Ω =>
        (fun i : ℕ => if i < 1 then τ i ω else 0) ∈ S))
    (hSucc : ∀ n : ℕ, ∃ S : Set (ℕ → ℝ), MeasurableSet S ∧
      (fun ω : Ω => N ω = n + 1) =ᵐ[P]
      (fun ω : Ω =>
        (fun i : ℕ => if i < n + 2 then τ i ω else 0) ∈ S)) :
    HasLaw (fun ω (j : ℕ) => τ (N ω + 1 + j) ω) μ P := by sorry
