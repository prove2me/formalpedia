-- Prove2me | solution 1 for e7_small_endpoint_moment_bound
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-08T07:04:04.108201+00:00
-- url     : https://prove2.me/submissions/182ce34f-a8f1-4008-9b02-be77c1a2c26c

import Mathlib

open MeasureTheory

theorem solution (G : ℝ → ℝ) (B T : ℝ)
    (hG : ∀ y, y ∈ Set.uIoc (0 : ℝ) (Real.exp (-T)) → ‖G y‖ ≤ B) :
    ‖∫ y in (0 : ℝ)..Real.exp (-T), G y‖ ≤ B * Real.exp (-T) := by
  have hpos : 0 < Real.exp (-T) := Real.exp_pos _
  rcases le_or_gt 0 B with hB | hB
  · have h := intervalIntegral.norm_integral_le_of_norm_le_const (f := G) hG
    rwa [sub_zero, abs_of_pos hpos] at h
  · exfalso
    have hy : Real.exp (-T) / 2 ∈ Set.uIoc (0 : ℝ) (Real.exp (-T)) := by
      rw [Set.uIoc_of_le hpos.le]
      constructor <;> linarith
    have hle := hG _ hy
    have hnorm : 0 ≤ ‖G (Real.exp (-T) / 2)‖ := norm_nonneg _
    linarith
