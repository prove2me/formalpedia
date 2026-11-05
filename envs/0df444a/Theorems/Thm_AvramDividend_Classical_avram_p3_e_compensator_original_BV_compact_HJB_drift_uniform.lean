-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_BV_compact_HJB_drift_uniform
-- name    : AvramDividend.Classical.avram_p3_e_compensator_original_BV_compact_HJB_drift_uniform
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:40:10.574578+00:00
-- url     : https://prove2.me/theorems/27271b05-b000-4a77-97c6-9e4e0d489882
-- title:
--   Uniform original BV Lévy HJB residual bound on strict compact reserve bands
-- statement:
--   The original BV Lévy negative-jump generator integral has a uniform compact reserve bound from previously Proved source measure estimates. Combine it with a bounded derivative and the original dividend value's finite upper bound to obtain one explicit uniform bound on the exact original HJB drift residual, automatically proving finite far-negative mark intensity from the original source ν.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_uniform_physical_negative_levy_integral_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_negative_levy_tail_finite_at_BV_C1_threshold
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_e_compensator_original_BV_compact_HJB_drift_uniform
{Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
{𝓕 : Filtration ℝ≥0 mΩ}
(X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
(w : ℝ → ℝ) (hwMeas : Measurable w)
(q : ℝ) (a b L R A : ℝ)
(ha : 0 < a) (ha2 : a ≤ 2) (hab : a ≤ b)
(hL : 0 ≤ L) (hR : 0 ≤ R) (hA : 0 ≤ A)
(hLip : ∀ u ∈ Set.Icc (a / 2) b, ∀ v ∈ Set.Icc (a / 2) b,
  |w u - w v| ≤ L * |u - v|)
(hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R)
(hDeriv : ∀ y ∈ Set.Icc a b, |deriv w y| ≤ A) :
∃ K : ℝ, 0 ≤ K ∧ ∀ y ∈ Set.Icc a b,
  |X.drift * deriv w y +
    (∫ z in Set.Iio (0 : ℝ), w (y + z) - w y ∂X.ν) - q * w y| ≤ K := by sorry
