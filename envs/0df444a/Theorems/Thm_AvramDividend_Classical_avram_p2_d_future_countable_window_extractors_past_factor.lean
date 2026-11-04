-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_countable_window_extractors_past_factor
-- name    : AvramDividend.Classical.avram_p2_d_future_countable_window_extractors_past_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:29:28.563019+00:00
-- url     : https://prove2.me/theorems/fb234f47-dcae-47eb-a412-88783f9a4665
-- title:
--   Countable original future marked-count windows with varying terminal times are jointly measurable and past-factorising
-- statement:
--   For countably many arbitrary Borel mark tests and deterministic future terminal times t_n≥s, construct jointly product-measurable functionals of the unchanged original future increment path, reproducing the exact jump counts on (s,t_n] and giving each original past-event expectation factorisation. Does not assume any ν-rate.
-- source:
--   Apply the Proved original future extractor and past-event factor theorem separately for each terminal time and Borel mark set, select the family by classical choice, and assemble product measurability using measurable_pi_iff.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_extractor_past_event_factor

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_countable_window_extractors_past_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (t : ℕ → ℝ≥0) (hst : ∀ n, s ≤ t n)
    (B : ℕ → Set ℝ) (hB : ∀ n, MeasurableSet (B n)) :
    ∃ F : ℕ → ((ℝ≥0 → ℝ) → ℝ≥0∞),
      Measurable (fun y : ℝ≥0 → ℝ => fun n : ℕ => F n y) ∧
      (∀ (n : ℕ) (ω : Ω),
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s (t n) ×ˢ B n) = F n (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω)) ∧
      (∀ (n : ℕ) (A : Set Ω), MeasurableSet[𝓕 s] A →
        (∫⁻ ω in A, F n (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω) ∂P) =
        P A * (∫⁻ ω, F n (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω) ∂P)) := by sorry
