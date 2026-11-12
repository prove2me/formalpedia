-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jb22_compact_clock_le_horizon
-- name    : AvramDividend.Classical.avram_jb22_compact_clock_le_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T08:22:58.686195+00:00
-- url     : https://prove2.me/theorems/71ae3b8b-c1fa-4b0f-ae9c-76f3f1eea8f9
-- title:
--   Original compact spatial clipped clock remains bounded by horizon
-- statement:
--   Every truncated compact-spatial clock obtained by min with a finite-horizon bounded stopping clock stays bounded by that horizon. This supplies the missing exact stopped-clock bound to the finite-cap reward integrability lemma.
-- source:
--   Direct deterministic ENNReal clipping fact required for the JB21 physical conditional budget's integrability component.

import Mathlib
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jb22_compact_clock_le_horizon
    {Ω : Type*} (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0))
    (ξ : ℕ → Ω → ℝ≥0∞) (κ : ℕ → Ω → ℝ≥0)
    (hκ : ∀ k ω, κ k ω =
      (min (ρ ω : ℝ≥0∞) (ξ k ω)).toNNReal) :
    ∀ k ω, κ k ω ≤ (n : ℝ≥0) := by sorry
