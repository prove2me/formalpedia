-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_finiteactivity_UBV_gaussian_sigma_positive
-- name    : AvramDividend.Classical.avram_f6_original_finiteactivity_UBV_gaussian_sigma_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T20:48:04.0898+00:00
-- url     : https://prove2.me/theorems/544833a4-bb18-4e96-b4ff-cef18c8806cd
-- title:
--   Finite jump activity plus original unbounded variation forces strictly positive Gaussian coefficient
-- statement:
--   For any exact original spectrally negative Lévy X with ν(-∞,0)<∞ and ¬BoundedVariation, σ>0. The source Proved result that purejump unbounded variation implies infinite negative activity rules out σ=0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_finiteactivity_UBV_gaussian_sigma_positive
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    0 < X.σ := by sorry
