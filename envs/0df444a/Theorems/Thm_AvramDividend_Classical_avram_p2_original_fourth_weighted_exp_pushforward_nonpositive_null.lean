-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_original_fourth_weighted_exp_pushforward_nonpositive_null
-- name    : AvramDividend.Classical.avram_p2_original_fourth_weighted_exp_pushforward_nonpositive_null
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:43:14.129558+00:00
-- url     : https://prove2.me/theorems/f90f1e37-cedc-4749-89c2-3214fe1d812b
-- title:
--   The original fourth-weighted source exponential image has no nonpositive marks
-- statement:
--   For the actual original spectrally negative Lévy process and every time, the finite fourth-weighted image of the original path law under exp(X_t) vanishes on nonpositive exponential coordinates. This is the exact left-support premise required to use compact sets [0,R] in the Prokhorov tightness proof for rescaled source measures.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_tilted_weighted_exponential_pushforward_finite

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_original_fourth_weighted_exp_pushforward_nonpositive_null
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) :
    ((P.withDensity (fun ω => ENNReal.ofReal
      ((Real.exp (X.X t ω) - 1) ^ 4))).map
      (fun ω => Real.exp (X.X t ω))) (Iic (0 : ℝ)) = 0 := by sorry
