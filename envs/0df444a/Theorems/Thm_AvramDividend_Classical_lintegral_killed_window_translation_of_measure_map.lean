-- Prove2me | Theorems.Thm_AvramDividend_Classical_lintegral_killed_window_translation_of_measure_map
-- name    : AvramDividend.Classical.lintegral_killed_window_translation_of_measure_map
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:30:44.868887+00:00
-- url     : https://prove2.me/theorems/1c65b156-fb6b-455d-b758-fdb544c7ff6e
-- title:
--   Translate a killed Stieltjes integral through a time-shifted measure and shifted stopping window
-- statement:
--   If the dividend measure is the push-forward of a future reward measure by addition of u, and a killed payment window is the translate of a future killed window, the nonnegative dividend integral over the original window equals the shifted future integral. This is the explicit window-preserving change of variables needed for strong-Markov barrier dividend valuation.
-- source:
--   W-free strong-Markov child 79978d61-9d1f-4b20-b8a5-114797a8e380: consumes the Proved pathwise full-dividend-measure shift 3093890e-4ed7-4198-8491-5f41d268763c and the future ruin-window shift to transport the actual killed reward. No scale assumptions.

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Restrict

open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.lintegral_killed_window_translation_of_measure_map
    (μ ν : Measure ℝ) (u : ℝ) (A B : Set ℝ)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hμ : μ = Measure.map (fun t : ℝ => u + t) ν)
    (hwindow : ∀ t : ℝ, u + t ∈ A ↔ t ∈ B)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ t in A, f t ∂μ) =
      ∫⁻ t in B, f (u + t) ∂ν := by
  sorry
