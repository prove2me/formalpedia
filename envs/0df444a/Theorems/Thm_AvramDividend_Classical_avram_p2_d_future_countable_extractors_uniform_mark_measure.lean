-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_countable_extractors_uniform_mark_measure
-- name    : AvramDividend.Classical.avram_p2_d_future_countable_extractors_uniform_mark_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:55:17.885209+00:00
-- url     : https://prove2.me/theorems/3ee99772-3c56-4b09-a210-57638f8cc979
-- title:
--   Countable original measurable future-mark extractors share one past-event mean mark measure
-- statement:
--   For a countable family of Borel mark tests and one original time window, construct all actual measurable shifted-future-path marked-count extractors jointly as a measurable coordinate map, while one genuine Borel mark mean measure ρ simultaneously gives the mean of every coordinate over every event in the original past filtration. The original source count is represented samplewise. No ν-rate is assumed.
-- source:
--   Use Proved countable original future extractor family b97e26c5 and Proved uniform original past-event Borel mark measure a34a29b0, transfer each restricted lintegral using exact samplewise extraction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_countable_extractors_uniform_mark_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : ℕ → Set ℝ) (hB : ∀ n, MeasurableSet (B n)) :
    ∃ (ρ : Measure ℝ) (F : ℕ → ((ℝ≥0 → ℝ) → ℝ≥0∞)),
      Measurable (fun y : ℝ≥0 → ℝ => fun n : ℕ => F n y) ∧
      (∀ (n : ℕ) (ω : Ω),
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ B n) =
          F n (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω)) ∧
      (∀ (n : ℕ) (A : Set Ω), MeasurableSet[𝓕 s] A →
        (∫⁻ ω in A, F n (fun v : ℝ≥0 =>
          X.X (s + v) ω - X.X s ω) ∂P) = P A * ρ (B n)) := by sorry
