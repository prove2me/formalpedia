-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_zero_poly_primitive_expectation
-- name    : AvramDividend.Classical.avram_wave5_04c_actual_bv_zero_poly_primitive_expectation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T15:36:48.744223+00:00
-- url     : https://prove2.me/theorems/21edf69a-fc21-4773-9fae-26cf96df9ad2
-- title:
--   Original BV Lévy polynomial primitive expectation equals finite exponential deficits
-- statement:
--   For the original spectrally negative bounded-variation Lévy source, identify the expectation of the integrated zero-constant polynomial derivative against the actual residual t*drift-X_t with a finite signed sum of exponential-deficit expectations, for every t≥0. The residual is measurable by source adaptedness and almost surely nonnegative by the Proved source finite-variation monotonicity. Exact polynomial integration and a separate rigorous Bochner finite-sum integrability interchange give the identity. There is no process replacement, coupling, arbitrary generator identity or second derivative.
-- source:
--   Remote standalone compiler candidates/work_on/AvramDividend_04c_original_BV_polynomial_primitive_expectation_standalone_check.lean; modular source candidates/work_on/AvramDividend_04c_original_BV_polynomial_primitive_expectation_interchange_probe.lean

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_zero_polynomial_primitive_finite_exp_deficits
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_nonnegative_random_residual_finite_exp_expectation
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04c_actual_bv_zero_poly_primitive_expectation {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) (p : Polynomial ℝ) (hp : Polynomial.eval 0 p = 0) (t : ℝ≥0) :
    (∫ ω, (∫ r in (0 : ℝ)..((t : ℝ) * X.drift - X.X t ω),
      Polynomial.eval (Real.exp (-r)) p) ∂P) =
      ∑ k ∈ p.support.erase 0, (p.coeff k / (k : ℝ)) *
        (1 - (∫ ω, Real.exp (-((k : ℝ) *
          ((t : ℝ) * X.drift - X.X t ω))) ∂P)) := by sorry
