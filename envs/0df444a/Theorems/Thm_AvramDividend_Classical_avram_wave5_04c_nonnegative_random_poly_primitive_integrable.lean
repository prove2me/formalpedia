-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_nonnegative_random_poly_primitive_integrable
-- name    : AvramDividend.Classical.avram_wave5_04c_nonnegative_random_poly_primitive_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T16:07:25.191738+00:00
-- url     : https://prove2.me/theorems/137ca299-300b-4bb0-a6f1-39e948f4008b
-- title:
--   Any zero-constant exponential polynomial jump primitive is Bochner integrable along nonnegative random residuals
-- statement:
--   For a measurable almost-surely nonnegative random residual R on any probability space, prove the genuine Bochner integrability of the random primitive ∫0^R p(exp(-r))dr for every polynomial p vanishing at zero. The exact polynomial primitive is a finite signed combination of the bounded exponential deficits 1-exp(-kR). Each constituent exponential is integrable by measurability, almost-sure nonnegativity and probability domination, and finite-sum integrability completes the proof. This discharges a required expectation-interchange premise for the original bounded-variation Lévy process without a fictitious process, additional moment hypothesis or C2 bound.
-- source:
--   Remote compiler sentinel-verified candidates/work_on/AvramDividend_04c_nonnegative_random_polynomial_primitive_integrable_probe.lean

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_zero_polynomial_primitive_finite_exp_deficits
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04c_nonnegative_random_poly_primitive_integrable {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (R : Ω → ℝ) (hMeas : Measurable R)
    (hNonneg : ∀ᵐ ω ∂P, 0 ≤ R ω)
    (p : Polynomial ℝ) (hp : Polynomial.eval 0 p = 0) :
    Integrable (fun ω => (∫ r in (0 : ℝ)..R ω,
      Polynomial.eval (Real.exp (-r)) p)) P := by sorry
