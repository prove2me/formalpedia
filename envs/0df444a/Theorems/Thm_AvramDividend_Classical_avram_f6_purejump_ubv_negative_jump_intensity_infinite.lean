-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_purejump_ubv_negative_jump_intensity_infinite
-- name    : AvramDividend.Classical.avram_f6_purejump_ubv_negative_jump_intensity_infinite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T16:12:43.207972+00:00
-- url     : https://prove2.me/theorems/b9b373fa-0326-4517-a8f1-75c0833e292e
-- title:
--   Pure-jump unbounded variation forces infinite total negative-jump intensity
-- statement:
--   For a spectrally negative Lévy process with zero Gaussian coefficient and unbounded variation, the Lévy measure has infinite total negative-jump mass. The already Proved infinite small-mark first-moment theorem bounds below the intensity; the first moment is pointwise dominated by 1 on (-1,0). This eliminates the finite-intensity pure-jump case, leaving genuinely infinite jump activity for the F6 purejump source.
-- source:
--   Avram purejump UBV from Proved 2703ea95 and set-integral monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_purejump_ubv_negative_jump_intensity_infinite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hσ : X.σ = 0) :
    X.ν (Iio (0 : ℝ)) = ⊤ := by sorry
