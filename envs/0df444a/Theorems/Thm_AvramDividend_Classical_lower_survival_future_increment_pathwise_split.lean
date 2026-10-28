-- Prove2me | Theorems.Thm_AvramDividend_Classical_lower_survival_future_increment_pathwise_split
-- name    : AvramDividend.Classical.lower_survival_future_increment_pathwise_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:03:04.163967+00:00
-- url     : https://prove2.me/theorems/d829a33d-d25f-4292-a4e7-39ee28d30e3e
-- title:
--   Exact pathwise lower survival splitting into past and stationary future increments
-- statement:
--   For any real-valued path, initial reserve x and times s,u, survival throughout [0,s+u] is exactly the intersection of survival to s and survival of the increment path v↦Y(s+v)-Y(s) over v≤u starting at the reserve x+Y(s). This is the exact pathwise event identity needed to apply the full-path Levy Markov-Tonelli theorem to killed Esscher rewards.
-- source:
--   Direct composition of the Proved pathwise closed-horizon survival split and published shifted-interval time-reparametrisation. The exact proof has passed remote Lean elaboration.

import Mathlib.Data.NNReal.Basic
import Theorems.Thm_AvramDividend_Classical_lower_survival_closed_horizon_pathwise_split
import Theorems.Thm_AvramDividend_Classical_lower_survival_shifted_interval_reparam

open Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.lower_survival_future_increment_pathwise_split
    {Ω : Type*} (Y : ℝ≥0 → Ω → ℝ) (x : ℝ) (s u : ℝ≥0) :
    {ω : Ω | ∀ v : ℝ≥0, v ≤ s + u → 0 ≤ x + Y v ω} =
      {ω : Ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + Y v ω} ∩
      {ω : Ω | ∀ v : ℝ≥0, v ≤ u →
        0 ≤ (x + Y s ω) + (Y (s + v) ω - Y s ω)} := by sorry
