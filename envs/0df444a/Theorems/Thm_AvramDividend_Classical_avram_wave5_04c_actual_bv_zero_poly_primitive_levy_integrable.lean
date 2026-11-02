-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_zero_poly_primitive_levy_integrable
-- name    : AvramDividend.Classical.avram_wave5_04c_actual_bv_zero_poly_primitive_levy_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T17:34:15.225207+00:00
-- url     : https://prove2.me/theorems/4ddc4982-0abb-48f8-9721-859d866d2154
-- title:
--   Genuine BV Lévy measure Bochner-integrability of zero-constant polynomial negative-jump primitives
-- statement:
--   For the genuine BV spectrally negative Lévy source, the full negative Lévy jump measure Bochner-integrates every primitive of a zero-constant exponential polynomial. This is a missing L1 interchange needed in the C1 generator-semigroup approximation, and follows by a finite signed sum of the proved integrable exponential deficits.
-- source:
--   The proved exact zero-constant polynomial primitive finite exponential deficit identity and bv_exponential_jump_integrable, combined by MeasureTheory.integrable_finset_sum on the full negative half-line.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_zero_polynomial_primitive_finite_exp_deficits
import Theorems.Thm_AvramDividend_Classical_bv_exponential_jump_integrable
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04c_actual_bv_zero_poly_primitive_levy_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (p : Polynomial ℝ) (hp : Polynomial.eval 0 p = 0) :
    IntegrableOn (fun y : ℝ =>
      ∫ r in (0 : ℝ)..(-y),
        Polynomial.eval (Real.exp (-r)) p)
      (Iio (0 : ℝ)) X.ν := by sorry
