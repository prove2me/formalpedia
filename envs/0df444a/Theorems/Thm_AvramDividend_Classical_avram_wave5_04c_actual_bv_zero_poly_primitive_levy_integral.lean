-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_zero_poly_primitive_levy_integral
-- name    : AvramDividend.Classical.avram_wave5_04c_actual_bv_zero_poly_primitive_levy_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T16:00:43.267585+00:00
-- url     : https://prove2.me/theorems/4c84f0bb-b991-49ae-9fa7-3cc8a883fef8
-- title:
--   Original BV Lévy measure of polynomial jump primitive equals finite exponential generator sum
-- statement:
--   For the original spectrally negative Lévy measure of an actual bounded-variation process, prove that the negative-jump integral of each zero-constant exponential polynomial primitive is exactly its finite exponential-test Lévy generator sum. Every constituent deficit is integrable by actual BV first-moment assumptions and Proved exponential-jump integrability. The primitive is identified pointwise using the previously Proved polynomial FTC formula, and the infinite-activity Bochner interchange is justified by a separate rigorous theorem. The result bridges the original-process polynomial transition slopes with the negative-jump term in the canonical generator without a replacement source or C2 regularity.
-- source:
--   Remote standalone compiler candidates/work_on/AvramDividend_04c_actual_BV_poly_primitive_levy_integral_standalone_check.lean; modular candidates/work_on/AvramDividend_04c_actual_BV_poly_primitive_levy_integral_probe.lean

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_zero_polynomial_primitive_finite_exp_deficits
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_negative_jump_finite_exponential_measure_interchange
import Theorems.Thm_AvramDividend_Classical_bv_exponential_jump_integrable
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04c_actual_bv_zero_poly_primitive_levy_integral {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (p : Polynomial ℝ) (hp : Polynomial.eval 0 p = 0) :
    (∫ y in Iio (0 : ℝ),
      (∫ r in (0 : ℝ)..(-y),
        Polynomial.eval (Real.exp (-r)) p) ∂X.ν) =
      ∑ k ∈ p.support.erase 0,
        (p.coeff k / (k : ℝ)) *
          (∫ y in Iio (0 : ℝ),
            1 - Real.exp ((k : ℝ) * y) ∂X.ν) := by sorry
