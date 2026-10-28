-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat08_countable_infimum_lower_bound_iff_all_lower_bounds
-- name    : AvramDividend.Classical.chat08_countable_infimum_lower_bound_iff_all_lower_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:33:15.983417+00:00
-- url     : https://prove2.me/theorems/ad9e7805-c5f6-468a-873c-6813aa494bb8
-- title:
--   Lower bound on a countable first-passage infimum iff every observation exceeds the bound
-- statement:
--   A countable infimum of extended nonnegative observation times stays above a bound exactly when each observation time does. This gives a pathwise no-detection-before-time criterion.
-- source:
--   Infimum lower-bound universal property.

import Mathlib.Probability.Process.Stopping

open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat08_countable_infimum_lower_bound_iff_all_lower_bounds
    {Ω : Type*} (τ : ℕ → Ω → WithTop ℝ≥0) (t : WithTop ℝ≥0) (ω : Ω) :
    t ≤ (⨅ k : ℕ, τ k ω) ↔ ∀ k : ℕ, t ≤ τ k ω := by sorry
