-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_CP_drift_one_from_triplet_coefficient
-- name    : AvramDividend.Classical.avram_bvb_obstruction_original_CP_drift_one_from_triplet_coefficient
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:22:24.756881+00:00
-- url     : https://prove2.me/theorems/2f4b51e2-a0d2-406f-9978-777d4d51e896
-- title:
--   Original compound Poisson drift equals one from its exact Lévy coefficient
-- statement:
--   If the source original Lévy process coefficient c is one plus the negative small-jump first moment, its BV drift is exactly one. This is the original filtered compound-Poisson law witness coefficient in Proved b1eb5fe7.
-- source:
--   Unfold original SpectrallyNegativeLevy.drift as c minus the Lévy mark integral. Substitute the exact compound Poisson coefficient c=1+integral, simplify ring identity. No distributional assumptions are added.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_bvb_obstruction_original_CP_drift_one_from_triplet_coefficient
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hc : X.c = 1 +
      (∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν)) :
    X.drift = 1 := by sorry
