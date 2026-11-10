-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_correct12_finitecap_generator_residual_floor
-- name    : AvramDividend.Classical.avram_bv_correct12_finitecap_generator_residual_floor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T07:58:36.1405+00:00
-- url     : https://prove2.me/theorems/1ecef407-d467-4f47-89d5-bae28e73bb71
-- title:
--   Original finite-cap BV HJB residual floor from local nonnegativity and finite negative jump activity
-- statement:
--   For the original finite-cap bounded-variation HJB candidate, finite negative jump activity provides a lower bound for the generator residual at each strictly interior reserve. Unlike the previously Proved global-positivity version, only the actual interior gradient, positive-reserve candidate and vanishing negative-reserve values are needed. The bound is relevant to integrability of the finite-activity original stopped HJB generator mesh and to original source theorem 8271cf4d.
-- source:
--   Source-exact finite-cap generator lower envelope for original 8271cf4d through 3993433e, 73419313 and assigned 51b72610. Remove the unimportable global nonnegativity premise from existing Proved e5e3c876 using the existing original positive-cap candidate nonnegativity theorem cb439447 and negative Levy support.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_full_negative_jump_increment_integrable
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_cap_C1_gradient_value_nonnegative_on_compact_interval
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_correct12_finitecap_generator_residual_floor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ z < 0, w z = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C →
      1 ≤ deriv w z)
    (hMass : X.ν (Iio (0 : ℝ)) < ⊤)
    (hDrift : 0 ≤ X.drift)
    (y : ℝ) (hy : 0 < y) (hyC : ENNReal.ofReal y < C)
    (hGen : X.GeneratorIntegrable w y) :
    -((X.ν (Iio (0 : ℝ))).toReal + q) * w y ≤
      X.generator w y - q * w y := by sorry
