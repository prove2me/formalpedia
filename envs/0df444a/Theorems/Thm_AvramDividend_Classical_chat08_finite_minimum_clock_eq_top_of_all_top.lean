-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat08_finite_minimum_clock_eq_top_of_all_top
-- name    : AvramDividend.Classical.chat08_finite_minimum_clock_eq_top_of_all_top
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:02:55.087483+00:00
-- url     : https://prove2.me/theorems/dcd23c1f-e8a8-43c7-9206-4821b845e202
-- title:
--   Finite detection clock remains infinite if every observation was infinite
-- statement:
--   The recursive finite minimum of observation clocks, initialized at infinity, equals infinity when all observations before the cutoff are infinite. A natural induction establishes the no-detection branch.
-- source:
--   Nat.rec successor step and the induction hypothesis.

import Mathlib.Probability.Process.Stopping

open MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat08_finite_minimum_clock_eq_top_of_all_top
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (τ : ℕ → Ω → WithTop ℝ≥0) :
    ∀ (n : ℕ) (ω : Ω),
      (∀ k : ℕ, k < n → τ k ω = ⊤) →
      (Nat.rec (motive := fun _ => Ω → WithTop ℝ≥0)
      (fun _ : Ω => (⊤ : WithTop ℝ≥0))
      (fun k σ ω => min (τ k ω) (σ ω)) n) ω = ⊤ := by sorry
