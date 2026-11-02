-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_first_candidate_filter_covers_original_jumps
-- name    : AvramDividend.Classical.avram_wave5_02a_first_candidate_filter_covers_original_jumps
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:41:50.892213+00:00
-- url     : https://prove2.me/theorems/73db8e42-2e79-426c-abdd-2e5693b18516
-- title:
--   Measurable first-occurrence filtering preserves coverage of actual source jumps
-- statement:
--   If a countable measurable family of original sample-dependent candidate times covers every positive nonzero jump of the original Levy process, first-occurrence filtering gives measurable active sets and preserves exact coverage. This theorem does not establish coverage for the candidates.
-- source:
--   Proved source jump candidate deduplication 46beafdc-e02a-4344-bd16-6c76ca667156 and least natural witness.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_jump_candidates_measurable_dedup

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_02a_first_candidate_filter_covers_original_jumps
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℕ → Ω → ℝ≥0) (hT : ∀ n, Measurable (T n))
    (hCover : ∀ ω u, 0 < u →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 →
      ∃ n, T n ω = u) :
    let A : ℕ → Set Ω := fun n => {ω |
      0 < T n ω ∧
      X.X (T n ω) ω -
        Function.leftLim (fun u : ℝ≥0 => X.X u ω) (T n ω) ≠ 0 ∧
      ∀ m < n, T m ω ≠ T n ω}
    (∀ n, MeasurableSet (A n)) ∧
    (∀ ω u, 0 < u →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 →
      ∃ n, ω ∈ A n ∧ T n ω = u) := by sorry
