-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_strict_physical_endpoint_cofinal_for_signed_fatou
-- name    : AvramDividend.Classical.avram_p3_grid4_strict_physical_endpoint_cofinal_for_signed_fatou
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T12:41:45.041195+00:00
-- url     : https://prove2.me/theorems/eae70d41-5558-4dc7-97d6-8c9043b595d4
-- title:
--   Cofinal strict stopped dividend-grid endpoints at the original horizon
-- statement:
--   The strictly pre-horizon physical grid endpoints T - T/(n+2) are increasing, nonnegative, bounded by T and cofinal strictly below T. This supplies exactly the scalar mesh hypotheses for the accepted source-exact signed random-error Fatou closure.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_strict_prefix_margin_sequence
open Classical MeasureTheory Set Filter AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_strict_physical_endpoint_cofinal_for_signed_fatou (T : ℝ) (hT : 0 < T) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let u : ℕ → ℝ := fun n => T - δ n
    Monotone u ∧ (∀ n, 0 ≤ u n) ∧
      (∀ n, u n ≤ T) ∧
      (∀ s : ℝ, s < T → ∃ n, s < u n) := by sorry
