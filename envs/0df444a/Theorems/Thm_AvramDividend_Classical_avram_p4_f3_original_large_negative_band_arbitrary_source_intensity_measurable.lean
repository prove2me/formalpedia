-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_large_negative_band_arbitrary_source_intensity_measurable
-- name    : AvramDividend.Classical.avram_p4_f3_original_large_negative_band_arbitrary_source_intensity_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T19:22:51.334785+00:00
-- url     : https://prove2.me/theorems/ce2f5916-170a-45eb-9a1a-6b0f3085a7b7
-- title:
--   Original separated large-negative Lévy quadratic jump intensity measurable on every physical source parameter
-- statement:
--   For the same original Levy measure and any measurable physical source reserve parameter, the squared large-negative-jump payoff coefficient has a measurable intensity on the source parameter space. This makes the full original separated-band large-jump source energy a genuine jointly measurable integral.
-- source:
--   Adapt the accepted original arbitrary-parameter measurable jump intensity construction 5ed70ebd, with the original full Levy SFinite proof and w measurable extension, using the original Iic(-epsilon) separated band.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Defs.Filter
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_zero_negative_payoff_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_full_levy_sfinite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_large_negative_band_arbitrary_source_intensity_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {S : Type*} [mS : MeasurableSpace S]
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (U : S → ℝ) (hU : Measurable U) (ε : ℝ) :
    Measurable (fun s =>
      (∫⁻ z in Iic (-ε),
        ENNReal.ofReal ((w (U s + z) - w (U s)) ^ 2) ∂X.ν)) := by sorry
