-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a28_cadlag_candidate_firstoccurrence_window_Borel_encard_eq_tsum_v2_20261116
-- name    : AvramDividend.Classical.avram_a28_cadlag_candidate_firstoccurrence_window_Borel_encard_eq_tsum_v2_20261116
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T17:38:04.929393+00:00
-- url     : https://prove2.me/theorems/5a6f4c67-9af2-43da-bd09-ad38a2e2dae9
-- title:
--   A càdlàg Borel marked-jump count on any half-open time window equals its deduplicated countable candidate-time series
-- statement:
--   For a càdlàg real path, a candidate-time enumeration covering each positive nonzero jump, and exact candidate jump marks, the Borel marked count on (s,T] equals a deduplicated ENNReal sum over candidate times. Import the Proved countable first-candidate cover cardinal lemma and canonical left-limit lemma. This is the source-exact deterministic identity needed to make arbitrary physical marked windows adapted, independent of probability assumptions.
-- source:
--   Proved countable first-candidate cover card equality 2880a35d and strict left-limit identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_a28_cadlag_candidate_firstoccurrence_window_Borel_encard_eq_tsum_v2_20261116
    (time : ℕ → (ℝ≥0 → ℝ) → ℝ≥0)
    (hCover : ∀ Y : ℝ≥0 → ℝ,
      (∀ u, ContinuousWithinAt Y (Ici u) u) →
      (∀ u, 0 < u →
        Tendsto Y (𝓝[<] u) (𝓝 (Function.leftLim Y u))) →
      ∀ u, 0 < u → Y u - Function.leftLim Y u ≠ 0 →
        ∃ k : ℕ, time k Y = u)
    (mark : ℕ → (ℝ≥0 → ℝ) → ℝ)
    (hExact : ∀ k (Y : ℝ≥0 → ℝ), 0 < time k Y →
      ContinuousWithinAt Y (Ici (time k Y)) (time k Y) →
      Tendsto Y (𝓝[<] (time k Y))
        (𝓝 (Function.leftLim Y (time k Y))) →
      mark k Y = Y (time k Y) - Function.leftLim Y (time k Y))
    (s T : ℝ≥0) (B : Set ℝ) :
    ∀ Y : ℝ≥0 → ℝ,
      (∀ u : ℝ≥0, ContinuousWithinAt Y (Ici u) u) →
      (∀ u : ℝ≥0, 0 < u →
        ∃ l : ℝ, Tendsto Y (𝓝[<] u) (𝓝 l)) →
      ({v : ℝ≥0 | s < v ∧ v ≤ T ∧
        Y v - Function.leftLim Y v ≠ 0 ∧
        Y v - Function.leftLim Y v ∈ B}).encard =
        ∑' k : ℕ,
          if s < time k Y ∧ time k Y ≤ T ∧ mark k Y ∈ B \ {0} ∧
              (∀ j : ℕ, j < k → time j Y ≠ time k Y)
          then (1 : ℝ≥0∞) else 0 := by sorry
