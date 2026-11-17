-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB294_sfinite_product_time_fibre_probability_envelope
-- name    : AvramDividend.Classical.avram_gbB294_sfinite_product_time_fibre_probability_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T07:58:45.91431+00:00
-- url     : https://prove2.me/theorems/8adcfb49-ff63-43f0-ac03-ac63dac77b80
-- title:
--   Product-time fibre integral envelope for sigma-finite first measure
-- statement:
--   Fubini-Tonelli envelope when the first product measure is sigma-finite; holds in particular for the Gaussian process probability measure and directly controls the original time-fibre occupation mass.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB294_sfinite_product_time_fibre_probability_envelope
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (S : Set (Ω × ℝ)) (hS : MeasurableSet S)
    (g : ℝ → ℝ≥0∞)
    (hFibre : ∀ t : ℝ, P ((fun ω : Ω => (ω, t)) ⁻¹' S) ≤ g t) :
    (P.prod volume) S ≤ ∫⁻ t : ℝ, g t ∂volume := by sorry
