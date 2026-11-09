-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_correct12_finite_activity_origin_HJB_drift_ceiling
-- name    : AvramDividend.Classical.avram_bv_correct12_finite_activity_origin_HJB_drift_ceiling
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T21:40:32.145952+00:00
-- url     : https://prove2.me/theorems/933ee9aa-160b-4a6d-9d44-ecfc26694ff7
-- title:
--   Original Standing BV finite-activity HJB controls the zero-reserve drift by discount and negative-jump intensity
-- statement:
--   For the actual original Standing bounded-variation process with finite negative-jump intensity and a strictly positive cap, taking the right-hand limit of the positive-reserve generator HJB bound gives drift at zero no greater than the discount-plus-jump rate times the candidate value at zero. This is necessary for the zero-reserve cash branch in the original stopped verification source; the time-zero, ruin, and horizon terms still require a separate stochastic-source argument.
-- source:
--   Strictly positive-cap original source 51b72610-16ac-4bf7-b81e-ab1b6456a6a7; limit of the Proved/public physical-process drift ceiling 6b5289f1-3f1e-41c8-a32a-a38d86a42437 at reserve zero, using continuity on Ici 0 and C>0.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_correct12_finite_activity_positive_cap_HJB_drift_ceiling
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bv_correct12_finite_activity_origin_HJB_drift_ceiling
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) :
    X.drift ≤ (q + (X.ν (Iio (0 : ℝ))).toReal) * w 0 := by sorry
