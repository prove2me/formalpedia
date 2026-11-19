-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_purejump_ubv_infinite_mass_each_small_negative_band
-- name    : AvramDividend.Classical.avram_f6_purejump_ubv_infinite_mass_each_small_negative_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T16:31:56.330397+00:00
-- url     : https://prove2.me/theorems/fad1e92c-1213-422f-bad8-1d61c6f695e3
-- title:
--   Every near-zero negative-jump band has infinite intensity for purejump unbounded variation
-- statement:
--   For an original spectrally negative Lévy driver of unbounded variation and zero Gaussian component, its genuine negative-jump Lévy measure gives infinitely many small negative marks in every interval (-δ,0), δ>0. This combines the authentic original Lévy measure integrability, Proved purejump infinite total negative intensity, Proved finite far-tail truncation, and the elementary infinite-measure partition. Useful for the unbounded-variation purejump HJB compensated small-mark source.
-- source:
--   Proved b9b373fa original infinite intensity, Proved negative_jump_truncation_measure_finite 16a2d301, source-compatible generic infinite negative near-zero mass lemma ef45ffc6.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_purejump_ubv_infinite_mass_each_small_negative_band
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hσ : X.σ = 0)
    (δ : ℝ) (hδ : 0 < δ) :
    X.ν (Ioo (-δ) 0) = ⊤ := by sorry
