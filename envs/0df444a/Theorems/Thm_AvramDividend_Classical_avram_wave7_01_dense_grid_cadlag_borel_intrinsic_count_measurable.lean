-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_dense_grid_cadlag_borel_intrinsic_count_measurable
-- name    : AvramDividend.Classical.avram_wave7_01_dense_grid_cadlag_borel_intrinsic_count_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T19:20:19.378936+00:00
-- url     : https://prove2.me/theorems/17d5a835-81c4-4a08-ac39-28ac01eec61d
-- title:
--   Any fixed countable dense source clock yields an exact measurable Borel-marked càdlàg jump count
-- statement:
--   Combines globally measurable two-sign first-downcrossing enumeration with exact dense-grid Borel marks and first-occurrence cardinality to obtain a genuine globally measurable extension of the intrinsic nonzero-jump count for any càdlàg path. Uses the given raw path and includes arbitrary Borel marks and infinite activity. The only remaining globalising step is existence of a dense countable clock and a positive vanishing scale.
-- source:
--   Proved original path candidate time enumeration 417d1996, exact first occurrence cardinality 2880a35d, canonical left-limit conversion 904bf313, and dense marked series 660f311b when Proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_two_sign_cadlag_measurable_candidate_time_enumeration
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_dense_grid_all_candidate_exact_marked_Borel_series
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_countable_first_candidate_cover_card_eq_dedup_sum
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_existing_strict_left_limit_is_canonical
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_wave7_01_dense_grid_cadlag_borel_intrinsic_count_measurable
    (grid : ℕ → ℝ≥0) (hdense : DenseRange grid)
    (pairs : ℕ → ℕ × ℚ) (hpairs : Function.Surjective pairs)
    (ε : ℕ → ℝ≥0) (hεpos : ∀ n, 0 < ε n)
    (hε : Tendsto ε atTop (𝓝 0))
    (T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
    ∃ F : (ℝ≥0 → ℝ) → ℝ≥0∞,
      Measurable F ∧
      ∀ Y : ℝ≥0 → ℝ,
        (∀ u : ℝ≥0, ContinuousWithinAt Y (Ici u) u) →
        (∀ u : ℝ≥0, 0 < u →
          ∃ l : ℝ, Tendsto Y (𝓝[<] u) (𝓝 l)) →
        (({v : ℝ≥0 | 0 < v ∧ v ≤ T ∧
          Y v - Function.leftLim Y v ≠ 0 ∧
          Y v - Function.leftLim Y v ∈ B}).encard : ℝ≥0∞) = F Y := by sorry
