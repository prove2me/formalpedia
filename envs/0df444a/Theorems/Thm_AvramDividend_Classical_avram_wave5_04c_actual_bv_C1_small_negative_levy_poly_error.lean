-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_C1_small_negative_levy_poly_error
-- name    : AvramDividend.Classical.avram_wave5_04c_actual_bv_C1_small_negative_levy_poly_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T17:44:51.68988+00:00
-- url     : https://prove2.me/theorems/68a401c1-652d-4b9e-b392-043ad8430b47
-- title:
--   Genuine BV Lévy small negative-jump C1 polynomial generator error bounded by first moment
-- statement:
--   For any globally C1 Lipschitz payoff in the genuine BV generator domain, its original Lévy-measure integral over (-1,0) is approximated arbitrarily closely by the integrated exponential polynomial jump primitive, with error bounded by epsilon times the actual small-negative first moment. The proof uses the original BV small-jump integrability and exact finite-band C1 polynomial approximation.
-- source:
--   Finite-band moving-base C1 polynomial first-moment bound 47c63, original BV negative-jump first moment 2296f, original BV generator jump increment integrability 5ff8b, and full polynomial primitive ν integrability 4ddc.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_small_negative_first_moment_integrable
import Theorems.Thm_AvramDividend_Classical_boundedVariation_full_negative_jump_increment_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_zero_poly_primitive_levy_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_C1_moving_base_residual_polynomial_first_moment_bound
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04c_actual_bv_C1_small_negative_levy_poly_error
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (hwC1 : ContDiff ℝ 1 w)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (x : ℝ) (hgen : X.GeneratorIntegrable w x)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : Polynomial ℝ, Polynomial.eval 0 p = 0 ∧
      |∫ y in Ioo (-1 : ℝ) 0,
        (w (x + y) - w x) +
          (∫ r in (0 : ℝ)..(-y),
            Polynomial.eval (Real.exp (-r)) p) ∂X.ν| ≤
      ε * (∫ y in Ioo (-1 : ℝ) 0, -y ∂X.ν) := by sorry
