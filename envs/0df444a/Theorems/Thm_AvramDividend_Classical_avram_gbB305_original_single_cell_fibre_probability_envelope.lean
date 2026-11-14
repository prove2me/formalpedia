-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB305_original_single_cell_fibre_probability_envelope
-- name    : AvramDividend.Classical.avram_gbB305_original_single_cell_fibre_probability_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:35:35.987122+00:00
-- url     : https://prove2.me/theorems/f3eb1c13-b605-40e9-98d3-acfb64fd0b72
-- title:
--   Original source single-cell probability-time mass is bounded by the integrated fibre probability envelope
-- statement:
--   For a probability space and jointly measurable sample-time event confined to one strictly open physical interval, if its original sample-section event probabilities are bounded by a nonnegative time envelope on that interval and vanish outside, its product probability-time mass is at most the integral of that envelope. This follows from Proved B294b genuine Tonelli and the interval indicator integral identity, and supplies the source-fibre-to-mass component of the genuine original Gaussian single-cell occupation B299.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB305_original_single_cell_fibre_probability_envelope
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (S : Set (Ω × ℝ)) (hS : MeasurableSet S)
    (a b : ℝ) (g : ℝ → ℝ≥0∞) (C : ℝ≥0∞)
    (hInside : ∀ t ∈ Set.Ioo a b,
      P ((fun ω : Ω => (ω, t)) ⁻¹' S) ≤ g t)
    (hOutside : ∀ t ∉ Set.Ioo a b,
      P ((fun ω : Ω => (ω, t)) ⁻¹' S) = 0)
    (hIntegral : (∫⁻ t in Set.Ioo a b, g t ∂volume) ≤ C) :
    (P.prod volume) S ≤ C := by sorry
