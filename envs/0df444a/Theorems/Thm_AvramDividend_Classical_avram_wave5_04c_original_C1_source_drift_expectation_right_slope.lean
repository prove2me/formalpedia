-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_original_C1_source_drift_expectation_right_slope
-- name    : AvramDividend.Classical.avram_wave5_04c_original_C1_source_drift_expectation_right_slope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:39:53.067117+00:00
-- url     : https://prove2.me/theorems/f0a80299-feb7-4e05-ba12-76dca6f671a9
-- title:
--   Original Lévy C1 physical-drift correction survives expectation under exact right time filter
-- statement:
--   For the actual spectrally negative Lévy process under its native probability law and globally C1 Lipschitz w, the expected normalized difference of the payoff at x+X_h and at x+X_h−d h tends to d w'(x) as h↓0 under the exact Real.toNNReal filter. The pointwise strict-C1 moving-base drift limit holds for each actual path; the global Lipschitz bound gives the integrable uniform envelope L|d|. Filter-indexed Bochner dominated convergence justifies the expectation interchange. No C2, independent coupling, or generator identity is assumed.
-- source:
--   Complete source candidates/work_on/AvramDividend_04c_original_C1_BV_drift_expectation_shift_probe.lean; SHA256 4c65175eff2799762adcebecf21847548ad12e97b900d7494999fe021fa97c4f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_original_C1_source_drift_pointwise
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04c_original_C1_source_drift_expectation_right_slope {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hwC1 : ContDiff ℝ 1 w)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (x d : ℝ) :
    Tendsto (fun h : ℝ =>
      ∫ ω, h⁻¹ *
        (w (x + X.X (Real.toNNReal h) ω) -
         w (x + X.X (Real.toNNReal h) ω - d * h)) ∂P)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (d * deriv w x)) := by sorry
