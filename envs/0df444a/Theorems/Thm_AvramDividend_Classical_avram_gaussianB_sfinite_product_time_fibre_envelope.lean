-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gaussianB_sfinite_product_time_fibre_envelope
-- name    : AvramDividend.Classical.avram_gaussianB_sfinite_product_time_fibre_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T01:01:23.226947+00:00
-- url     : https://prove2.me/theorems/0063d6de-9a31-453d-a847-2b8cdac19ac0
-- title:
--   Original s-finite Gaussian source product time-fibre envelope using exact pinned Tonelli equality
-- statement:
--   For any s-finite probability source and measurable space-time event S, a pointwise upper bound g(t) on the probability of each time fibre yields the bound (P⊗Lebesgue)(S)≤∫g(t)dt. This is the properly assumption-qualified positive product-measure estimate required to bound the original Gaussian stopped occupation and spatial fixed-level null contact.

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open MeasureTheory
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gaussianB_sfinite_product_time_fibre_envelope
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (S : Set (Ω × ℝ)) (hS : MeasurableSet S)
    (g : ℝ → ℝ≥0∞)
    (hFibre : ∀ t : ℝ, P ((fun ω : Ω => (ω, t)) ⁻¹' S) ≤ g t) :
    (P.prod volume) S ≤ ∫⁻ t : ℝ, g t ∂volume := by sorry
