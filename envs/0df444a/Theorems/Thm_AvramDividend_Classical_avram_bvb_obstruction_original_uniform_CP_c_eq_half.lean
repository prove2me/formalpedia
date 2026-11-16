-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_uniform_CP_c_eq_half
-- name    : AvramDividend.Classical.avram_bvb_obstruction_original_uniform_CP_c_eq_half
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:27:49.632576+00:00
-- url     : https://prove2.me/theorems/13d9c64d-4568-4017-96d0-7d4f0f575d87
-- title:
--   Original negative-uniform unit-rate compound Poisson Lévy coefficient equals one half
-- statement:
--   For the exact source triplet coefficient c=1+∫z ν(dz) with ν uniform negative-unit marks, the original Lévy small-jump coefficient c is 1/2. This supplies the precise coefficient hypothesis for the completed original positive-reserve HJB reduction.
-- source:
--   The actual original uniform-negative mark integral with restriction of the restricted measure equals −1/2 by Proved source lemma e9c5375c and Measure.restrict_restrict. Substitute in c=1+integral, simplify.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_uniform_negative_levy_mark_mean_half
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_bvb_obstruction_original_uniform_CP_c_eq_half
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hc : X.c = 1 + (∫ z in Ioo (-1 : ℝ) 0,
      z ∂((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)))) :
    X.c = 1 / 2 := by sorry
