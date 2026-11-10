-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_finite_activity_origin_derivative_uniform_closed_radius_HJB
-- name    : AvramDividend.Classical.avram_bv_zero13_finite_activity_origin_derivative_uniform_closed_radius_HJB
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T08:13:56.061283+00:00
-- url     : https://prove2.me/theorems/d87602cd-a428-4c0c-8fd9-4cd5c04319c5
-- title:
--   Original finite BV activity HJB derivative uniform bound up to the finite cap boundary
-- statement:
--   Under the exact original Standing finite-negative-activity BV generator and positive interior HJB hypotheses, for every positive radius whose ENNReal value is at most the cap, the C1 derivative has a uniform absolute bound at every strictly interior positive point below the radius. The radius itself may equal the finite positive cap, and no differentiability of the value at the cap or zero is assumed. The original physical generator local drift estimate and the Proved closed endpoint secant provide the envelope.
-- source:
--   Necessary original finite-cap zero-to-cap cutoff interface; adapts accepted 4a65a38a but uses the source-exact Proved aeec073e closed endpoint slope to permit radius equal to cap.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_avram_bv_correct12_finite_activity_local_generator_drift_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_cap_C1_gradient_linear_lower_envelope
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_cap_C1_closed_endpoint_two_point_jump_envelope
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_zero13_finite_activity_origin_derivative_uniform_closed_radius_HJB
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (ε : ℝ) (hε : 0 < ε) (hεC : ENNReal.ofReal ε ≤ C) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ y : ℝ, 0 < y → y < ε → |deriv w y| ≤ K := by sorry
