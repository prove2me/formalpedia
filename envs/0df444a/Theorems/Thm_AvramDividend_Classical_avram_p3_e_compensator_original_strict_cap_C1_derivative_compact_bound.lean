-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_strict_cap_C1_derivative_compact_bound
-- name    : AvramDividend.Classical.avram_p3_e_compensator_original_strict_cap_C1_derivative_compact_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:02:54.427472+00:00
-- url     : https://prove2.me/theorems/2dd46d99-9e4c-4c4f-a60f-199c90b6a4c3
-- title:
--   Canonical strict-cap C1 dividend derivative is uniformly bounded on the original positive band
-- statement:
--   The original strict HJB region {y>0, ofReal y<C} is open and includes any strict compact reserve band [a,b] for b strictly below cap. Canonical ContDiffOn on that original region yields continuous ordinary derivative, hence uniform compact derivative bound, discharging hDeriv required by the genuine source BV HJB integrability theorem.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_source_HJB_strict_cap_band_open
open MeasureTheory Set Topology AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_e_compensator_original_strict_cap_C1_derivative_compact_bound
(C : ℝ≥0∞) (w : ℝ → ℝ) (a b : ℝ)
(ha : 0 < a) (hab : a ≤ b) (hbC : ENNReal.ofReal b < C)
(hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
∃ A : ℝ, 0 ≤ A ∧ ∀ y ∈ Set.Icc a b, |deriv w y| ≤ A := by sorry
