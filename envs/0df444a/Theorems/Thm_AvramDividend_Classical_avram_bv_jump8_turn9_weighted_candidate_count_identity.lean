-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn9_weighted_candidate_count_identity
-- name    : AvramDividend.Classical.avram_bv_jump8_turn9_weighted_candidate_count_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T08:31:51.690721+00:00
-- url     : https://prove2.me/theorems/9d6c1eb9-08b7-4bec-8161-74b880c41b19
-- title:
--   Weighted mapped counting integral equals deduplicated source-exact candidate series
-- statement:
--   Generic weighted bridge from proved count-map lintegral-to-tsum baf85154 and first occurrence reindexing 27229df0; no Poisson assumptions.
-- source:
--   Generic weighted bridge from proved count-map lintegral-to-tsum baf85154 and first occurrence reindexing 27229df0; no Poisson assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_bv_jump8_turn9_weighted_candidate_count_identity
    (T : ℝ≥0) (g : ℝ → ℝ≥0∞) (hg : Measurable g)
    (time : ℕ → (ℝ≥0 → ℝ) → ℝ≥0)
    (mark : ℕ → (ℝ≥0 → ℝ) → ℝ)
    (hCandidate : ∀ Y : ℝ≥0 → ℝ,
      (∀ u : ℝ≥0, ContinuousWithinAt Y (Ici u) u) →
        (∀ u : ℝ≥0, 0 < u → ∃ l : ℝ, Tendsto Y (𝓝[<] u) (𝓝 l)) →
        (∀ k : ℕ, 0 < time k Y →
          mark k Y = Y (time k Y) - Function.leftLim Y (time k Y)) ∧
        (∀ u : ℝ≥0, 0 < u → Y u - Function.leftLim Y u ≠ 0 →
          ∃ k : ℕ, time k Y = u)) :
    ∀ Y : ℝ≥0 → ℝ,
      (∀ u : ℝ≥0, ContinuousWithinAt Y (Ici u) u) →
        (∀ u : ℝ≥0, 0 < u → ∃ l : ℝ, Tendsto Y (𝓝[<] u) (𝓝 l)) →
      (∑' k : ℕ,
        if 0 < time k Y ∧ time k Y ≤ T ∧
            (∀ j : ℕ, j < k → time j Y ≠ time k Y)
        then (if mark k Y = 0 then 0 else g (mark k Y))
        else 0) =
      ∫⁻ p : ℝ≥0 × ℝ,
        if 0 < p.1 ∧ p.1 ≤ T then g p.2 else 0 ∂
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ Y u - Function.leftLim Y u ≠ 0}).map
          (fun u => (u, Y u - Function.leftLim Y u))) := by sorry
