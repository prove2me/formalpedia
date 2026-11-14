-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB294_original_product_time_fibre_probability_envelope
-- name    : AvramDividend.Classical.avram_gbB294_original_product_time_fibre_probability_envelope
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T23:16:53.718335+00:00
-- url     : https://prove2.me/theorems/2416b84e-1f01-49d8-a101-21cc6e469321
-- title:
--   Original section probability bounds integrate to a product probability-time event bound
-- statement:
--   For any original sample probability measure and jointly measurable sample-by-real-time event, a pointwise upper envelope on the original sample-section probability yields a product probability-time mass bound by the physical-time integral of that envelope. The proof is exact product Tonelli and lintegral monotonicity, supporting B266 Gaussian good-cell probability integration.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB294_original_product_time_fibre_probability_envelope
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (S : Set (Ω × ℝ)) (hS : MeasurableSet S)
    (g : ℝ → ℝ≥0∞)
    (hFibre : ∀ t : ℝ, P ((fun ω : Ω => (ω, t)) ⁻¹' S) ≤ g t) :
    (P.prod volume) S ≤ ∫⁻ t : ℝ, g t ∂volume := by sorry
