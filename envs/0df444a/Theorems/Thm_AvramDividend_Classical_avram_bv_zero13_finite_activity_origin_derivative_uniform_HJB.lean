-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_finite_activity_origin_derivative_uniform_HJB
-- name    : AvramDividend.Classical.avram_bv_zero13_finite_activity_origin_derivative_uniform_HJB
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T07:23:23.501203+00:00
-- url     : https://prove2.me/theorems/4a65a38a-cc65-4d87-b510-7950dba0f54d
-- title:
--   Original finite activity BV HJB uniform C1 derivative control on every positive half-band touching zero
-- statement:
--   For the original Standing bounded-variation spectrally negative Levy source with finite negative jump intensity, positive discount rate and positive barrier cap, and a nonnegative-at-origin candidate satisfying zero-negative values, continuous nonnegative half-line, C1 positive interior, original generator HJB inequality and derivative lower bound at least one, the absolute derivative has a finite uniform upper bound on all 0<y<=epsilon whenever epsilon is a positive subcap reserve. The bound comes quantitatively from original physical drift and finite negative jump intensity; no generator at zero, auxiliary process, or signed-generator L1 is assumed.
-- source:
--   Root-connected zero-cutoff regularity from Proved original local generator drift bound e6d7e520, physical drift positivity 0432f641, positive C1 linear envelope f138f64f and two-point secant aeec073e; required for zero spatial cutoff removal in original finite-activity BV stopped expected HJB source.

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

theorem AvramDividend.Classical.avram_bv_zero13_finite_activity_origin_derivative_uniform_HJB
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
    (ε : ℝ) (hε : 0 < ε) (hεC : ENNReal.ofReal ε < C) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ y : ℝ, 0 < y → y ≤ ε → |deriv w y| ≤ K := by sorry
