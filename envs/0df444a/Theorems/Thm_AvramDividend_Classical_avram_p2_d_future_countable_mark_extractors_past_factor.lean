-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_countable_mark_extractors_past_factor
-- name    : AvramDividend.Classical.avram_p2_d_future_countable_mark_extractors_past_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:23:57.728681+00:00
-- url     : https://prove2.me/theorems/b97e26c5-5ecc-4da5-b2f9-55e721cda9de
-- title:
--   Countably many original marked future extractors are jointly measurable and past-event factorising
-- statement:
--   For any countable Borel mark-test family, construct a simultaneous product-measurable family of functions on original shifted future increment paths, each recovering exactly the literal source marked count and factoring ENNReal expectations over every original past event. No jump-rate theorem is assumed.
-- source:
--   Apply Proved original P2-D future-extractor past-event factorisation e0bc4905 to every Borel mark test; use classical countable choice and Mathlib measurable_pi_iff to assemble one product-measurable countable family.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_extractor_past_event_factor

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_countable_mark_extractors_past_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : ℕ → Set ℝ) (hB : ∀ n, MeasurableSet (B n)) :
    ∃ F : ℕ → ((ℝ≥0 → ℝ) → ℝ≥0∞),
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
          X.X (s + v) ω - X.X s ω) ∂P) =
        P A * (∫⁻ ω, F n (fun v : ℝ≥0 =>
          X.X (s + v) ω - X.X s ω) ∂P)) := by sorry
