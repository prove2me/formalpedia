-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_normalised_negative_mark_laplace_and_rate_20261117
-- name    : AvramDividend.Classical.avram_a27_original_normalised_negative_mark_laplace_and_rate_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T16:28:50.0705+00:00
-- url     : https://prove2.me/theorems/12e9396b-68f9-4048-8c30-f7eeb7307026
-- title:
--   Original single negative mark Laplace moment is within unit interval with exact Lévy rate balance
-- statement:
--   For the original spectrally negative Lévy jump intensity with finite nonzero negative activity, each nonnegative-tilt negative-mark exponential normalized by the actual negative intensity lies between zero and one. Its Poisson rate factor recovers the exact negative-mark Lévy exponential integral.
-- source:
--   Source negative intensity positivity, finite negative mark exponential bound and integrability, and finite-mark exponential-excess integral identity. All source measures unchanged.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The single physical negative mark Laplace moment has correct normalized intensity. -/

theorem AvramDividend.Classical.avram_a27_original_normalised_negative_mark_laplace_and_rate_20261117
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) (hNu : X.ν ≠ 0)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    ∃ m : ℝ, 0 ≤ m ∧ m ≤ 1 ∧
      (X.ν (Iio (0 : ℝ))).toReal * (m - 1) =
        (∫ y in Iio (0 : ℝ),
          Real.exp (θ * y) - 1 ∂X.ν) := by sorry
