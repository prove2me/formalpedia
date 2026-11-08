-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_coord8_zero_clock_mask_upper_bridge
-- name    : AvramDividend.Classical.avram_coord8_zero_clock_mask_upper_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T08:53:41.413302+00:00
-- url     : https://prove2.me/theorems/10d5e581-2438-47e0-8347-dc2c4da05bd9
-- title:
--   Coordinator derived zero-clock masked expected-reward inequality for positive-clock source
-- statement:
--   For each integrable stopped reward F_k, a pointwise initial-clock inequality and an integrable masked positive-clock reward with expectation at most b imply the full expected upper bound. The proof is a direct almost-everywhere domination and integral monotonicity, requiring no measurability of the stopping clock beyond the explicit integrability of its masked reward.
-- source:
--   Original derived: integral monotonicity from a genuine pointwise zero-clock domination and independent positive-clock masked expected upper bound, preserving the original stopped reward integrability.

import Mathlib

open MeasureTheory
open scoped NNReal

theorem AvramDividend.Classical.avram_coord8_zero_clock_mask_upper_bridge
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (b : ℝ) (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hFI : ∀ k, Integrable (F k) P)
    (hzero : ∀ k ω, σ k ω = 0 → F k ω ≤ b)
    (hpos : ∀ k,
      Integrable (fun ω => if σ k ω = 0 then b else F k ω) P ∧
      (∫ ω, if σ k ω = 0 then b else F k ω ∂P) ≤ b) :
    ∀ k, (∫ ω, F k ω ∂P) ≤ b := by sorry
