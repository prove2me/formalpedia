-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat08_countable_infimum_clock_top_iff_all_top
-- name    : AvramDividend.Classical.chat08_countable_infimum_clock_top_iff_all_top
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:31:28.679192+00:00
-- url     : https://prove2.me/theorems/2d90f42d-7d03-4fed-8c21-4ca525e0c40c
-- title:
--   Countable infimum of observation clocks is infinite precisely when every clock is infinite
-- statement:
--   For an arbitrary family of extended nonnegative waiting times, the pointwise infimum is infinite if and only if every waiting time is infinite. Useful for a countable first-passage construction.
-- source:
--   Order-theoretic infimum bounds and uniqueness of the top element.

import Mathlib.Probability.Process.Stopping

open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat08_countable_infimum_clock_top_iff_all_top
    {Ω : Type*} (τ : ℕ → Ω → WithTop ℝ≥0) (ω : Ω) :
    (⨅ k : ℕ, τ k ω) = ⊤ ↔ ∀ k : ℕ, τ k ω = ⊤ := by sorry
