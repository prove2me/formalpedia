-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_C1_random_residual_poly_error_integrable
-- name    : AvramDividend.Classical.avram_wave5_04c_C1_random_residual_poly_error_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T16:17:00.032217+00:00
-- url     : https://prove2.me/theorems/76d9a175-ab66-49f6-8a7c-2c84acf46489
-- title:
--   Global C1 random jump decrement minus polynomial primitive is Bochner integrable
-- statement:
--   The global Lipschitz bound dominates each random C1 payoff decrement by L times the genuinely integrable random residual. The polynomial primitive is independently proved integrable under probability domination and almost-sure nonnegativity. Thus their difference is a genuine Bochner-integrable random error. This is a precise expectation-interchange premise for the BV generator-semigroup bridge, with no second derivative or surrogate process.
-- source:
--   Remote candidate candidates/work_on/AvramDividend_04c_C1_random_residual_poly_error_integrable_probe.lean

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_nonnegative_random_poly_primitive_integrable
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04c_C1_random_residual_poly_error_integrable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (R : Ω → ℝ) (hMeas : Measurable R) (hNonneg : ∀ᵐ ω ∂P, 0 ≤ R ω) (hInt : Integrable R P) (w : ℝ → ℝ) (hwC1 : ContDiff ℝ 1 w) (L : ℝ) (hL : 0 ≤ L) (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|) (p : Polynomial ℝ) (hp : Polynomial.eval 0 p = 0) (y : ℝ) :
    Integrable (fun ω => (w y - w (y - R ω)) -
      (∫ r in (0 : ℝ)..R ω,
        Polynomial.eval (Real.exp (-r)) p)) P := by sorry
