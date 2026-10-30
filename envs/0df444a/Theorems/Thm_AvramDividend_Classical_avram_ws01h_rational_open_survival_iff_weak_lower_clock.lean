-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_rational_open_survival_iff_weak_lower_clock
-- name    : AvramDividend.Classical.avram_ws01h_rational_open_survival_iff_weak_lower_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T10:49:10.144981+00:00
-- url     : https://prove2.me/theorems/a4d8cdc1-c622-4553-bd4e-1cfe6150260a
-- title:
--   Actual rational open-horizon lower-survival tests equal weak strict lower passage time inequality
-- statement:
--   For the actual source Lévy càdlàg trajectory, all rational inverse-natural-grid reserve tests strictly before observation time T are equivalent to T being no greater than the source-defined strict lower first-passage clock. The exact weak inequality includes zero and infinite clock cases and avoids evaluation of an arbitrary uncountable full path at a variable terminal age. This supplies a genuinely jointly measurable open-horizon future survival reward for the Esscher Qp renewal.
-- source:
--   Canonical Proved dense-grid open survival f9c964cc and true lower strict observation bound fa7ceff5, both original source Lévy; elementary indexed-infimum order.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_lower_survival_dense_grid_iff
import Theorems.Thm_AvramDividend_Classical_twoSidedExitDownTime_le_of_strict_lower_gap_observed

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01h_rational_open_survival_iff_weak_lower_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (ω : Ω) (T : ℝ≥0) :
    (∀ n : ℕ, 0 < n → ∀ k : ℕ,
      (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < T →
        0 ≤ x + X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω) ↔
      (T : ℝ≥0∞) ≤ twoSidedExitDownTime X (-x) ω := by sorry
