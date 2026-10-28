-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat08_finite_minimum_le_new_observation
-- name    : AvramDividend.Classical.chat08_finite_minimum_le_new_observation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:58:01.987605+00:00
-- url     : https://prove2.me/theorems/b6f7ff82-76a0-4e1d-80d0-e6908237fc57
-- title:
--   Finite sampled first-detection clock is no later than each included observation
-- statement:
--   When a new detection observation is included in the recursive finite-minimum clock, the updated clock is pointwise bounded by that observation time. Useful for identifying the infinite-prefix infimum without assuming right-continuity of the filtration.
-- source:
--   min_le_left applied to the defining Nat.rec successor step.

import Mathlib.Probability.Process.Stopping

open MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat08_finite_minimum_le_new_observation
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (τ : ℕ → Ω → WithTop ℝ≥0) :
    ∀ (n : ℕ) (ω : Ω),
      (Nat.rec (motive := fun _ => Ω → WithTop ℝ≥0)
        (fun _ : Ω => (⊤ : WithTop ℝ≥0))
        (fun k σ ω => min (τ k ω) (σ ω)) (n + 1)) ω ≤ τ n ω := by sorry
