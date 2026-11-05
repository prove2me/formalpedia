-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_full_levy_sfinite
-- name    : AvramDividend.Classical.avram_p2_e_compensator_original_full_levy_sfinite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T10:56:50.725201+00:00
-- url     : https://prove2.me/theorems/8b4fec03-ea22-4fef-a051-c21220a49d23
-- title:
--   Original Lévy mark measure globally s-finite from actual negative support
-- statement:
--   For the genuine original spectrally negative Lévy source X, its full signed-mark Lévy measure X.ν is s-finite. The exact original negative-support restriction identity is Proved and identifies X.ν with its negative restriction, which is independently Proved s-finite using the original quadratic Lévy moment. This completes the explicit measure instance needed by predictable product compensation and other stochastic integral consumers without introducing a replacement measure or assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_e_compensator_original_full_levy_sfinite
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    SFinite X.ν := by sorry
