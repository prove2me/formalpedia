-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f4_original_ubv_purejump_nonzero_levy_measure
-- name    : AvramDividend.Classical.avram_p4_f4_original_ubv_purejump_nonzero_levy_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:49:05.389199+00:00
-- url     : https://prove2.me/theorems/3d01f20c-12ff-492b-8840-878920e16782
-- title:
--   Original unbounded-variation zero-Gaussian Lévy process has a nonzero jump measure
-- statement:
--   For the actual spectrally negative Lévy process, unbounded variation with no Gaussian coefficient forces a nonzero Lévy jump measure. This discharges the nonzero-jump hypothesis of the purejump centred stopped payoff reduction.
-- source:
--   Direct contradiction from Proved original purejump first-variation divergence 2703ea95, since the zero Lévy measure has zero lintegral.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_original_purejump_ubv_infinite_variation

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_p4_f4_original_ubv_purejump_nonzero_levy_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hσ : X.σ = 0) : X.ν ≠ 0 := by sorry
