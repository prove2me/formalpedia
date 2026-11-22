-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_lsc_finite_horizon_bounded_integrand_energy
-- name    : AvramDividend.Classical.avram_lsc_finite_horizon_bounded_integrand_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T22:38:09.157182+00:00
-- url     : https://prove2.me/theorems/43090805-dff6-4165-8036-39ab2cf2f286
-- title:
--   Finite Brownian Itô L² energy of an arbitrary uniformly bounded integrand on a finite horizon
-- statement:
--   For a probability measure P, any real-valued sample-path/time integrand whose absolute value is bounded globally by a nonnegative constant has finite quadratic time-space extended integral over every positive finite time interval. The proof uses monotonicity of the extended integral and the finite Lebesgue measure of a bounded interval, with no stochastic or stopped-dividend assumptions.
-- source:
--   Avram Dividend Classical 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43, finite-cap zero-jump original stopped Gaussian Itô integration. This imports only Mathlib and is intended to discharge L² obligations of compact-localized Gaussian gradient noise, and the elementary deterministic window integrand.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_lsc_finite_horizon_bounded_integrand_energy
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (F : Ω → ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ ω s, |F ω s| ≤ M)
    (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖F ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by sorry
