-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn9_measurable_exact_cadlag_selectors
-- name    : AvramDividend.Classical.avram_bv_jump8_turn9_measurable_exact_cadlag_selectors
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T08:31:51.388017+00:00
-- url     : https://prove2.me/theorems/bc17f40a-148f-4cda-9aba-348c3b349001
-- title:
--   Measurable exact candidate times and marks for all real càdlàg paths
-- statement:
--   Source geometric selector from proved two-sign rational-grid coverage 417d1996 and exact mark reconstruction 660f311b.
-- source:
--   Source geometric selector from proved two-sign rational-grid coverage 417d1996 and exact mark reconstruction 660f311b.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_bv_jump8_turn9_measurable_exact_cadlag_selectors :
    ∃ (time : ℕ → (ℝ≥0 → ℝ) → ℝ≥0)
      (mark : ℕ → (ℝ≥0 → ℝ) → ℝ),
      (∀ k, Measurable (time k)) ∧
      (∀ k, Measurable (mark k)) ∧
      ∀ Y : ℝ≥0 → ℝ,
        (∀ u : ℝ≥0, ContinuousWithinAt Y (Ici u) u) →
        (∀ u : ℝ≥0, 0 < u → ∃ l : ℝ, Tendsto Y (𝓝[<] u) (𝓝 l)) →
        (∀ k : ℕ, 0 < time k Y →
          mark k Y = Y (time k Y) - Function.leftLim Y (time k Y)) ∧
        (∀ u : ℝ≥0, 0 < u → Y u - Function.leftLim Y u ≠ 0 →
          ∃ k : ℕ, time k Y = u) := by sorry
