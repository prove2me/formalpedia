-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_clock_mark_laplace_exact_rate_20261117
-- name    : AvramDividend.Classical.avram_a27_original_physical_clock_mark_laplace_exact_rate_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T16:45:48.155004+00:00
-- url     : https://prove2.me/theorems/7e30288e-5534-4d25-a6d8-66dec475b6c4
-- title:
--   Original physical Poisson count rate and normalized negative-mark moment recover exact horizon Levy exponent
-- statement:
--   Given the original physical finite negative-jump Poisson rate expressed in ENNReal, there is a bounded one-mark Laplace moment whose Poisson mass rate exactly equals the horizon-scaled Levy negative-mark exponential integral. No stochastic mark-stream independence is needed for this rate balance.
-- source:
--   Original normalized mark moment, real finite-rate ENNReal clock/intensity cast and elementary ring identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original physical Poisson negative-mark moment has the exact horizon-scaled Levy rate. -/

theorem AvramDividend.Classical.avram_a27_original_physical_clock_mark_laplace_exact_rate_20261117
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) (hNu : X.ν ≠ 0)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ)
    (r : ℝ≥0)
    (hRate : (r : ℝ) =
      ((t : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal) :
    ∃ m : ℝ, 0 ≤ m ∧ m ≤ 1 ∧
      (r : ℝ) * (m - 1) =
        (t : ℝ) *
          (∫ y in Iio (0 : ℝ),
            Real.exp (θ * y) - 1 ∂X.ν) := by sorry
