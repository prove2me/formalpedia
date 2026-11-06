-- Prove2me | solution 1 for prelim_decay
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:04:20.326196+00:00
-- url     : https://prove2.me/submissions/96f763b4-0c84-4481-82f4-325e81b11ad9

import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

open Real MeasureTheory FourierTransform

theorem solution (ψ : ℝ → ℂ) (u : ℝ) : ‖𝓕 (ψ : ℝ → ℂ) u‖ ≤ ∫ t, ‖ψ t‖ := by
  exact VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 volume (innerₗ ℝ) ψ u
