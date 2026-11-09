-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_correct12_finite_activity_positive_cap_HJB_drift_ceiling
-- name    : AvramDividend.Classical.avram_bv_correct12_finite_activity_positive_cap_HJB_drift_ceiling
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T20:23:05.740656+00:00
-- url     : https://prove2.me/theorems/6b5289f1-3f1e-41c8-a32a-a38d86a42437
-- title:
--   Original Standing BV finite-activity drift bounded by positive-cap HJB value and jump intensity
-- statement:
--   For the original Standing BV process with finite negative jump activity, the positive cap HJB and gradient assumptions imply that the physical positive premium drift is bounded at every strictly positive reserve below the cap by the candidate value multiplied by discount plus jump intensity. Negative jump destinations are nonnegative by the positive-cap affine lower envelope and the zero extension below ruin. This is the core origin cash ceiling for the corrected BV source route.
-- source:
--   Direct dependency on newly Proved/public e6d7e520 and original positive-cap gradient lower-envelope f138f64f; intended lower-origin boundary estimate for original Open 51b72610.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_cap_C1_gradient_linear_lower_envelope
import Theorems.Thm_AvramDividend_Classical_avram_bv_correct12_finite_activity_local_generator_drift_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_correct12_finite_activity_positive_cap_HJB_drift_ceiling
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
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (y : ℝ) (hy : 0 < y) (hyC : ENNReal.ofReal y < C) :
    X.drift ≤ (q + (X.ν (Iio (0 : ℝ))).toReal) * w y := by sorry
