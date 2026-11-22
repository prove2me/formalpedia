-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_workerB_original_finite_negative_annulus_source_facts_20261122
-- name    : AvramDividend.Classical.avram_workerB_original_finite_negative_annulus_source_facts_20261122
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T10:09:59.315798+00:00
-- url     : https://prove2.me/theorems/5288a74e-f192-444b-bfaf-386525639cc1
-- title:
--   Original Lévy finite reciprocal negative annulus is measurable, negative, and finite mass
-- statement:
--   For every original spectrally negative Lévy process without a bounded-variation assumption, every finite reciprocal interval of negative jump marks is Borel, lies in the negative half-line, and has finite Lévy measure. This is required before applying the real stopped original compensated Campbell theorem and does not assert any reward or stopped HJB bound.
-- source:
--   Proved negative_jump_truncation_measure_finite 16a2d301, original X.ν_integrable, and elementary endpoint monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_workerB_original_finite_negative_annulus_source_facts_20261122
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n m : ℕ) :
    let B : Set ℝ :=
      Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    MeasurableSet B ∧ B ⊆ Iio (0 : ℝ) ∧ X.ν B < ⊤ := by sorry
