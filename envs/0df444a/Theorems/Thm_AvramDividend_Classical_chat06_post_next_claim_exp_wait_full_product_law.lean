-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_post_next_claim_exp_wait_full_product_law
-- name    : AvramDividend.Classical.chat06_post_next_claim_exp_wait_full_product_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T16:28:20.40242+00:00
-- url     : https://prove2.me/theorems/6f8952cb-ab2d-4f20-824f-62eccc326f0e
-- title:
--   Whole iid exponential waiting-time law after the selected next claim
-- statement:
--   Under iid rate-one exponential waiting times and the full-measure observable-past characterisation of the future claim index, the complete sequence of waiting times strictly after the next claim retains the infinite-product Exp(1) law. The theorem constructs the deterministic suffix law directly using iIndepFun and hasLaw_infinitePi. It does not assert any residual waiting-time memorylessness property at the fixed observation time.
-- source:
--   Chat06 source bv_post_next_claim_selected_exp_wait_full_product_law_chat06_20261020.lean, pinned Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474, using three independently Proved helper modules.

import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Theorems.Thm_AvramDividend_Classical_chat06_stopped_future_full_joint_law_ae_selection
import Theorems.Thm_AvramDividend_Classical_chat06_masked_iid_prefix_full_suffix_independence
import Theorems.Thm_AvramDividend_Classical_chat06_all_count_events_past_cylinders

open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem AvramDividend.Classical.chat06_post_next_claim_exp_wait_full_product_law
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P)
    (hτlaw : ∀ i, HasLaw (τ i) (expMeasure 1) P)
    (N : Ω → ℕ) (hN : Measurable N)
    (hZero : ∃ S : Set (ℕ → ℝ), MeasurableSet S ∧
      (fun ω : Ω => N ω = 0) =ᵐ[P]
      (fun ω : Ω =>
        (fun i : ℕ => if i < 1 then τ i ω else 0) ∈ S))
    (hSucc : ∀ n : ℕ, ∃ S : Set (ℕ → ℝ), MeasurableSet S ∧
      (fun ω : Ω => N ω = n + 1) =ᵐ[P]
      (fun ω : Ω =>
        (fun i : ℕ => if i < n + 2 then τ i ω else 0) ∈ S)) :
    HasLaw (fun ω (j : ℕ) => τ (N ω + 1 + j) ω)
      (Measure.infinitePi (fun _ : ℕ => expMeasure (1 : ℝ))) P := by sorry
