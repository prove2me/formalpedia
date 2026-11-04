-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_extractor_uniform_past_mark_mean_measure
-- name    : AvramDividend.Classical.avram_p2_d_future_extractor_uniform_past_mark_mean_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:43:44.25998+00:00
-- url     : https://prove2.me/theorems/7daa6bbd-ba03-466d-9684-d19d4a1fdcf0
-- title:
--   Original measurable future marked extractor factors past-event means against one Borel mark measure
-- statement:
--   For any original Lévy process and Borel mark class, there exist one genuine mark measure ρ and an explicitly measurable functional F of the true future-increment path which reproduces the original intrinsic jump count for every sample and whose mean restricted to every original past event equals P(A)*ρ(B). No identification with X.ν is assumed.
-- source:
--   The Proved original future-path extractor 5cf3e058 and P2-D Proved single-measure past-event count factor a34a29b0; convert the restricted lintegral by pointwise hExact, preserving the original X,P,𝓕.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_extractor_uniform_past_mark_mean_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) :
    ∃ (ρ : Measure ℝ) (F : (ℝ≥0 → ℝ) → ℝ≥0∞),
      Measurable F ∧
      (∀ ω : Ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) =
        F (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω)) ∧
      (∀ (A : Set Ω), MeasurableSet[𝓕 s] A →
        (∫⁻ ω in A, F (fun v : ℝ≥0 =>
          X.X (s + v) ω - X.X s ω) ∂P) = P A * ρ B) := by sorry
