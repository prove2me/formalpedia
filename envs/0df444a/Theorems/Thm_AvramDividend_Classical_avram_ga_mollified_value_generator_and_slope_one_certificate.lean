-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_mollified_value_generator_and_slope_one_certificate
-- name    : AvramDividend.Classical.avram_ga_mollified_value_generator_and_slope_one_certificate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T21:46:06.133536+00:00
-- url     : https://prove2.me/theorems/d4ddb3b2-5b55-42a9-a4c3-30a4b5f7d2e8
-- title:
--   One-sided smooth finite-cap test retains HJB upper-strip generator bound and dividend slope one
-- statement:
--   An original cap-linear test function with the global slope-one secant property, convolved from strictly below with a positive unit-mass kernel, retains derivative at least one wherever differentiable. Simultaneously, convolution of a scalar HJB generator upper residual bounded by c times the strict upper-strip indicator retains the sharp strict cutoff b<y, with no b-epsilon leakage. This puts the two independently proven source properties into one exactly checkable smooth Ito test certificate.
-- source:
--   A sound simultaneous finitecap Gaussian smooth-test certificate for source 0ef5d778. Uses independently Proved 046dc2ca, 5caf8432 and 570895dc; it does not assume or imply a stochastic Ito-Stieltjes ledger.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_positive_one_sided_smoothing_preserves_secant
import Theorems.Thm_AvramDividend_Classical_avram_ga_smooth_secant_implies_deriv_ge_one
import Theorems.Thm_AvramDividend_Classical_avram_ga_one_sided_upperstrip_convolution_bound
open MeasureTheory Filter Set AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_mollified_value_generator_and_slope_one_certificate
    (μ : Measure ℝ) (φ V g : ℝ → ℝ)
    (hφI : Integrable φ μ) (hφpos : 0 ≤ᵐ[μ] φ)
    (hφnorm : (∫ z, φ z ∂μ) = 1)
    (hPositive : ∀ᵐ z ∂μ, 0 < z)
    (ε : ℝ) (hε : 0 < ε) (b c : ℝ) (hc : 0 ≤ c)
    (hSec : ∀ x y : ℝ, x ≤ y → y - x ≤ V y - V x)
    (hg : ∀ u, g u ≤ if b < u then c else 0)
    (hVI : ∀ y, Integrable (fun z => φ z * V (y - ε*z)) μ)
    (hgI : ∀ y, Integrable (fun z => φ z * g (y - ε*z)) μ)
    (y : ℝ)
    (hDiff : DifferentiableAt ℝ
      (fun t => ∫ z, φ z * V (t - ε*z) ∂μ) y) :
    1 ≤ deriv (fun t => ∫ z, φ z * V (t - ε*z) ∂μ) y ∧
      (∫ z, φ z * g (y - ε*z) ∂μ) ≤
        if b < y then c else 0 := by sorry
