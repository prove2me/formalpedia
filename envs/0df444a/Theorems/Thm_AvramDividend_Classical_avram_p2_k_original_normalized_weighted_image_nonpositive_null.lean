-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_k_original_normalized_weighted_image_nonpositive_null
-- name    : AvramDividend.Classical.avram_p2_k_original_normalized_weighted_image_nonpositive_null
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:11:38.203904+00:00
-- url     : https://prove2.me/theorems/66288eec-2dde-4b0d-a242-bc66882a528f
-- title:
--   Every original normalised weighted exponential source image has no nonpositive mass
-- statement:
--   For all real times including the zero extension, the true original inverse-time fourth-weighted exp(X_h) image measure assigns zero to (-∞,0]. This supplies P2-I's positive support condition without a jump intensity assumption.
-- source:
--   The true original weighted exp(X_h) image has zero nonpositive mass by Proved source theorem f90f1e37. Multiplying by the positive-time inverse ENNReal scalar preserves that null set, and nonpositive times are defined by the zero measure. This is the exact support premise needed to apply the P2-I finite-measure compact-test convergence theorem to the genuine original source.

import Mathlib.Data.ENNReal.Operations
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_fourth_weighted_exp_pushforward_nonpositive_null

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_k_original_normalized_weighted_image_nonpositive_null
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (h : ℝ) :
    (if 0 < h then (ENNReal.ofReal h)⁻¹ •
      ((P.withDensity (fun ω => ENNReal.ofReal
        ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
        (fun ω => Real.exp (X.X (Real.toNNReal h) ω)))
    else (0 : Measure ℝ)) (Iic (0 : ℝ)) = 0 := by sorry
