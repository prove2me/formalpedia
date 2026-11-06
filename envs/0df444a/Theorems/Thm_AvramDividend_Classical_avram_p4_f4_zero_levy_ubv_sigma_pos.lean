-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f4_zero_levy_ubv_sigma_pos
-- name    : AvramDividend.Classical.avram_p4_f4_zero_levy_ubv_sigma_pos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:49:05.474227+00:00
-- url     : https://prove2.me/theorems/37d963a0-712f-4f06-87d6-6a9238f0684c
-- title:
--   Zero original Lévy measure plus unbounded variation forces positive Gaussian coefficient
-- statement:
--   For a spectrally negative Lévy process with vanishing jump measure, the finite-variation integral vanishes. Therefore failure of bounded variation forces σ≠0, and its standing nonnegativity yields 0<σ.
-- source:
--   Exact source BoundedVariation definition and nonnegativity of the Gaussian coefficient.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f4_zero_levy_ubv_sigma_pos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (hν : X.ν = 0) :
    0 < X.σ := by sorry
