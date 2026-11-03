-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_two_sign_cadlag_measurable_candidate_time_enumeration
-- name    : AvramDividend.Classical.avram_wave7_01_two_sign_cadlag_measurable_candidate_time_enumeration
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T19:03:44.514489+00:00
-- url     : https://prove2.me/theorems/417d1996-803e-49b9-a80c-baab54d1d672
-- title:
--   One measurable countable raw-path selector sequence covers all positive càdlàg jump times
-- statement:
--   Interleave the globally product-measurable rational first-downcrossing candidate-time sequences for a càdlàg real path and its negation. Every positive nonzero jump time, of either sign, occurs as an indexed value. No finite activity, Lévy law, altered path or replacement sample space is used; the selector is measurable on all raw coordinate paths.
-- source:
--   Proved original-source rational first-downcrossing product measurability ed9c2972 and genuine two-sign càdlàg coverage eadc9439; measurability of path negation by Measurable.of_eval; even/odd interleaving.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_all_cadlag_jumps_two_rational_downcrossing_families
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_countable_rational_first_downcrossing_time_sequence_product_measurable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_two_sign_cadlag_measurable_candidate_time_enumeration
    (grid : ℕ → ℝ≥0) (hdense : DenseRange grid)
    (pairs : ℕ → ℕ × ℚ) (hpairs : Function.Surjective pairs) :
    ∃ time : ℕ → (ℝ≥0 → ℝ) → ℝ≥0,
      (∀ k, Measurable (time k)) ∧
      ∀ Y : ℝ≥0 → ℝ,
        (∀ u : ℝ≥0, ContinuousWithinAt Y (Ici u) u) →
        (∀ u : ℝ≥0, 0 < u →
          Tendsto Y (𝓝[<] u) (𝓝 (Function.leftLim Y u))) →
        ∀ u : ℝ≥0, 0 < u →
          Y u - Function.leftLim Y u ≠ 0 →
          ∃ k : ℕ, time k Y = u := by sorry
