-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_zero_polynomial_residual_exp_deficit_right_slope
-- name    : AvramDividend.Classical.avram_wave5_04c_actual_bv_zero_polynomial_residual_exp_deficit_right_slope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T15:21:44.256985+00:00
-- url     : https://prove2.me/theorems/da28d4e7-94de-465e-8a6b-03b5d782fa78
-- title:
--   Original BV residual right slope for exact polynomial primitive exponential coefficients
-- statement:
--   For the original bounded-variation spectrally negative Lévy process and a polynomial with zero constant term, specialise the already Proved finite signed residual exponential-test slope to the precise coefficients p.coeff(k)/k appearing in the exact integrated polynomial primitive. The finite index set is p.support.erase 0, so all retained modes are strictly positive integers. This is an exact original-process generator identity with no process replacement, no coupling and no extra assumptions. It supplies the explicit stochastic half of the finite-band C1 approximation.
-- source:
--   Remote proof source candidates/work_on/AvramDividend_04c_original_BV_polynomial_exp_deficit_right_slope_probe.lean

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_finite_signed_exponential_right_slope
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04c_actual_bv_zero_polynomial_residual_exp_deficit_right_slope {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) (p : Polynomial ℝ) (hp : Polynomial.eval 0 p = 0) :
    Tendsto
      (fun h : ℝ => ∑ k ∈ p.support.erase 0,
        (p.coeff k / (k : ℝ)) * (h⁻¹ * (1 -
          (∫ ω, Real.exp ((k : ℝ) *
            (-((Real.toNNReal h : ℝ) * X.drift -
              X.X (Real.toNNReal h) ω))) ∂P))))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∑ k ∈ p.support.erase 0,
        (p.coeff k / (k : ℝ)) *
          (∫ y in Iio (0 : ℝ), 1 - Real.exp ((k : ℝ) * y) ∂X.ν))) := by sorry
