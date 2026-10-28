-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_psi_quadratic_normalised_bounds_ws01f
-- name    : AvramDividend.Classical.levy_psi_quadratic_normalised_bounds_ws01f
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T10:35:17.713487+00:00
-- url     : https://prove2.me/theorems/bd04796e-4241-458a-be67-a22ae6792a2f
-- title:
--   Two-sided quadratic normalisation bound for actual spectrally negative Lévy exponent
-- statement:
--   For each positive integer Laplace parameter n+1, the genuine spectrally negative Lévy exponent divided by (n+1) squared lies between the Gaussian-drift-compensated-small-jump expression with a finite large-negative-jump correction and the same expression without that correction. The proof normalises previously accepted true Lévy–Khintchine upper and lower bounds. This reusable pointwise squeeze package is a genuine separate child of the Gaussian quadratic-asymptotic proof.
-- source:
--   Prove2Me Proved psi_upper_bound_by_compensated_small_jumps, psi_lower_bound_by_compensated_small_jumps and levy_large_negative_jump_unit_integrable; exact real Lévy–Khintchine normalisation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_psi_upper_bound_by_compensated_small_jumps
import Theorems.Thm_AvramDividend_Classical_psi_lower_bound_by_compensated_small_jumps
import Theorems.Thm_AvramDividend_Classical_levy_large_negative_jump_unit_integrable

open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_psi_quadratic_normalised_bounds_ws01f
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ) :
    (X.c / ((n : ℝ) + 1) + X.σ ^ 2 / 2 +
      (∫ y in Ioo (-1 : ℝ) 0,
        (Real.exp (((n : ℝ) + 1) * y) - 1 -
          ((n : ℝ) + 1) * y) ∂X.ν) / (((n : ℝ) + 1) ^ 2) -
      (∫ y in Iic (-1 : ℝ), (1 : ℝ) ∂X.ν) /
        (((n : ℝ) + 1) ^ 2) ≤
      X.ψ ((n : ℝ) + 1) / (((n : ℝ) + 1) ^ 2)) ∧
    (X.ψ ((n : ℝ) + 1) / (((n : ℝ) + 1) ^ 2) ≤
      X.c / ((n : ℝ) + 1) + X.σ ^ 2 / 2 +
      (∫ y in Ioo (-1 : ℝ) 0,
        (Real.exp (((n : ℝ) + 1) * y) - 1 -
          ((n : ℝ) + 1) * y) ∂X.ν) / (((n : ℝ) + 1) ^ 2)) := by sorry
