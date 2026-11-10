-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_finite_activity_closed_both_boundaries_HJB_lipschitz
-- name    : AvramDividend.Classical.avram_bv_zero13_finite_activity_closed_both_boundaries_HJB_lipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T08:16:40.85021+00:00
-- url     : https://prove2.me/theorems/73d0c52e-adba-40c0-aaf3-e88178714f0d
-- title:
--   Original finite BV activity HJB closed zero to finite cap boundary Lipschitz envelope
-- statement:
--   The true original finite-negative-activity Standing bounded-variation process supports a finite Lipschitz envelope for the candidate value on every CLOSED interval from zero to a positive reserve radius at most the cap. This includes the finite cap endpoint without asserting differentiability or generator validity at either boundary. It follows from the closed-radius interior derivative ceiling and the Proved closed endpoint lower slope, plus continuity on the half-line.
-- source:
--   Root-connected finite-cap spatial cutoff source-exact interface: use the closed-radius derivative theorem and aeec073e on closed intervals, allowing the endpoint to equal finite cap. No stochastic Ito or cash identity is claimed.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_finite_activity_origin_derivative_uniform_closed_radius_HJB
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_cap_C1_closed_endpoint_two_point_jump_envelope
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_zero13_finite_activity_closed_both_boundaries_HJB_lipschitz
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
      ∀ y ∈ Icc (0 : ℝ) ε, ∀ z ∈ Icc (0 : ℝ) ε,
        |w z - w y| ≤ K * |z - y| := by sorry
