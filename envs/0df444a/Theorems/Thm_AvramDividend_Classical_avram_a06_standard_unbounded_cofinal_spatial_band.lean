-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_standard_unbounded_cofinal_spatial_band
-- name    : AvramDividend.Classical.avram_a06_standard_unbounded_cofinal_spatial_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T17:39:16.812523+00:00
-- url     : https://prove2.me/theorems/130604bc-73ef-4b59-b42c-b5a3bac02bb6
-- title:
--   A06 canonical unbounded cofinal original-reserve spatial bands
-- statement:
--   For every original dividend cap C (including the infinite cap), any interior reserve y with y positive and its extended-real value below C eventually belongs to the increasing compact spatial bands [0,k+1]. This supplies a single concrete cofinal spatial localisation for the existing source-exact original BV physical bad-band theorems, removing any separately quantified band-exhaustion hypothesis in subsequent stopped cash/HJB reductions. It uses the Archimedean property and preserves all original Lévy objects.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a06_standard_unbounded_cofinal_spatial_band
    (C : ℝ≥0∞) :
    ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ k ≥ N, y ∈ Icc (0 : ℝ) ((k : ℝ) + 1) := by sorry
