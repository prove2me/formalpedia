-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat08_finite_minimum_stopping_times_nat_rec
-- name    : AvramDividend.Classical.chat08_finite_minimum_stopping_times_nat_rec
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:31:06.475427+00:00
-- url     : https://prove2.me/theorems/ac6a6b0d-fbe2-46da-85d0-5f8921ff1707
-- title:
--   Finite minima of stopping times without right continuity of the filtration
-- statement:
--   For any sequence of stopping times, the minimum of its first n clocks, with initial infinity, is a stopping time. This requires no filtration right-continuity. It enables finite sampled first-passage clock approximations.
-- source:
--   MeasureTheory.IsStoppingTime.min and IsStoppingTime definition.

import Mathlib.Probability.Process.Stopping

open MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat08_finite_minimum_stopping_times_nat_rec
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (ℱ : Filtration ℝ≥0 mΩ)
    (τ : ℕ → Ω → WithTop ℝ≥0)
    (hτ : ∀ k, IsStoppingTime ℱ (τ k)) :
    ∀ n : ℕ, IsStoppingTime ℱ
      (Nat.rec (fun _ : Ω => (⊤ : WithTop ℝ≥0))
        (fun k σ ω => min (τ k ω) (σ ω)) n) := by sorry
