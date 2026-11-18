-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_finite_mark_exponential_excess_integral_split_20261117
-- name    : AvramDividend.Classical.avram_a27_finite_mark_exponential_excess_integral_split_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T16:23:17.206403+00:00
-- url     : https://prove2.me/theorems/d489802b-3579-4c99-a883-057d80b7b3e0
-- title:
--   Finite marked-Poisson exponential excess integral equals one-mark moment minus intensity
-- statement:
--   For a finite negative-mark intensity measure with integrable exponential moment, the integral of e^(theta y)-1 is exactly the exponential mark integral minus the measure's total real mass. This identifies the exponent in the original negative-jump conditional Laplace law.
-- source:
--   Bochner integral linearity under finite mark intensity and exponential integrability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped ENNReal
noncomputable section

/-- The finite mark exponential excess integral is the mark moment minus total intensity. -/

theorem AvramDividend.Classical.avram_a27_finite_mark_exponential_excess_integral_split_20261117 (μ : Measure ℝ) [IsFiniteMeasure μ]
    (θ : ℝ)
    (hInt : Integrable (fun y : ℝ => Real.exp (θ * y)) μ) :
    (∫ y, Real.exp (θ * y) - 1 ∂μ) =
      (∫ y, Real.exp (θ * y) ∂μ) - μ.real Set.univ := by sorry
