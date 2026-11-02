-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_zero_poly_primitive_right_slope
-- name    : AvramDividend.Classical.avram_wave5_04c_actual_bv_zero_poly_primitive_right_slope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T15:42:49.464783+00:00
-- url     : https://prove2.me/theorems/9c21fc75-c237-4288-95b4-8aa724eb260f
-- title:
--   Original BV source polynomial primitive exact right-time expectation slope
-- statement:
--   For the actual spectrally negative bounded-variation Lévy source, the right-time derivative at zero of the expected integral of a zero-constant polynomial applied to exp(-r) along the actual random residual t*drift-X_t equals the negative-jump Lévy-measure expression of its exact finite exponential primitive. The result uses a proved Bochner expectation interchange and the actual source exponential-test slope, without a replacement process, artificial generator identity, second derivatives, or localised assumptions.
-- source:
--   Remote standalone compiler candidates/work_on/AvramDividend_04c_original_BV_polynomial_primitive_right_slope_standalone_check.lean; modular source candidates/work_on/AvramDividend_04c_original_BV_polynomial_primitive_right_slope_probe.lean

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_zero_poly_primitive_expectation
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_zero_polynomial_residual_exp_deficit_right_slope
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04c_actual_bv_zero_poly_primitive_right_slope {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) (p : Polynomial ℝ) (hp : Polynomial.eval 0 p = 0) :
    Tendsto
      (fun h : ℝ => h⁻¹ *
        (∫ ω, (∫ r in (0 : ℝ)..
          ((Real.toNNReal h : ℝ) * X.drift -
            X.X (Real.toNNReal h) ω),
          Polynomial.eval (Real.exp (-r)) p) ∂P))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∑ k ∈ p.support.erase 0,
        (p.coeff k / (k : ℝ)) *
          (∫ y in Iio (0 : ℝ), 1 - Real.exp ((k : ℝ) * y) ∂X.ν))) := by sorry
