-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_generic_negative_mark_window_integral_formula
-- name    : AvramDividend.Classical.avram_mix_gauss14_generic_negative_mark_window_integral_formula
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T11:11:47.607912+00:00
-- url     : https://prove2.me/theorems/e914b9c9-d168-42f6-82d2-63aee6dd54b3
-- title:
--   Generic negative marked time-window integral is the negative of a Borel nonnegative marked mass
-- statement:
--   For every measure on physical time and real jump marks, any measurable nonpositive spatial Borel band and deterministic left-open right-closed window, the signed real marked integral equals the negative real part of its positive ENNReal mass. This is the reusable source-exact algebraic bridge for transporting signed original negative jump integrals to their genuine shifted-path versions without auxiliary noise.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_negative_integral_eq_neg_lintegral_toReal
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_gauss14_generic_negative_mark_window_integral_formula
    (μ : Measure (ℝ≥0 × ℝ)) (a b : ℝ≥0) (B : Set ℝ)
    [DecidablePred (· ∈ B)] (hB : MeasurableSet B) (hNeg : ∀ z ∈ B, z ≤ 0) :
    (∫ p in (Ioc a b ×ˢ B), p.2 ∂μ) =
      -((∫⁻ p : ℝ≥0 × ℝ,
        if a < p.1 ∧ p.1 ≤ b then
          (if p.2 ∈ B then ENNReal.ofReal (-p.2) else 0) else 0 ∂μ).toReal) := by sorry
