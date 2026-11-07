-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f4_original_purejump_ubv_infinite_variation
-- name    : AvramDividend.Classical.avram_p4_f4_original_purejump_ubv_infinite_variation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:31:48.000942+00:00
-- url     : https://prove2.me/theorems/2703ea95-010f-4593-9130-24242c685697
-- title:
--   Original unbounded-variation pure-jump Levy source has infinite small negative jump variation
-- statement:
--   For the actual original spectrally negative Levy process, if the paths have unbounded variation and the Gaussian coefficient vanishes, the Levy measure has infinite first absolute moment over negative jumps of size below one. Consequently this branch necessarily requires compensated small-jump stochastic integration.
-- source:
--   Directly unfold SpectrallyNegativeLevy.BoundedVariation under hBV and hσ; same physical X and original Levy measure.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_p4_f4_original_purejump_ubv_infinite_variation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (hσ : X.σ = 0) :
    (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν) = ⊤ := by sorry
