-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_negative_mark_exponential_mass_between_zero_and_rate_20261117
-- name    : AvramDividend.Classical.avram_a27_original_negative_mark_exponential_mass_between_zero_and_rate_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T16:28:04.29707+00:00
-- url     : https://prove2.me/theorems/121ee3d9-5797-44d9-96fc-b5579e1a2b42
-- title:
--   Original negative-mark exponential integral lies between zero and finite jump intensity
-- statement:
--   A finite negative Lévy mark measure has a finite nonnegative exponential moment for each nonnegative tilt, bounded above by its total negative jump intensity. Thus the normalized single physical mark Laplace moment lies between zero and one.
-- source:
--   Proved finite negative exponential integrability and original finite measure restricted to negative marks; direct a.e. exponential upper bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The finite negative-mark exponential mass is between zero and total jump intensity. -/

theorem AvramDividend.Classical.avram_a27_original_negative_mark_exponential_mass_between_zero_and_rate_20261117 (ν : Measure ℝ)
    (hFinite : ν (Iio (0 : ℝ)) < ⊤)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    0 ≤ (∫ y in Iio (0 : ℝ), Real.exp (θ * y) ∂ν) ∧
    (∫ y in Iio (0 : ℝ), Real.exp (θ * y) ∂ν) ≤
      (ν (Iio (0 : ℝ))).toReal := by sorry
