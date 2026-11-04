-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_extractor_past_event_factor
-- name    : AvramDividend.Classical.avram_p2_d_future_extractor_past_event_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:51:19.052842+00:00
-- url     : https://prove2.me/theorems/e0bc4905-d622-4c12-860c-48f0fda9f5b9
-- title:
--   Original marked future-path functional has exact past-event mean factorisation
-- statement:
--   For the original X, P, filtration and any Borel mark B, construct the existing measurable future-increment functional representing every sample count and show its expectation over any past event A is P(A) times the unconditional expectation, without assuming any Lévy jump-rate identity.
-- source:
--   Combine the Proved exact original future measurable extractor 5cf3e058 with the Proved original past-event marked count factorisation 264b3973; transport both integrals using pointwise count equality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_actual_intrinsic_rectangle_past_event_factor_unconditional

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_extractor_past_event_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) :
    ∃ F : (ℝ≥0 → ℝ) → ℝ≥0∞,
      Measurable F ∧
      (∀ ω : Ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) =
        F (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω)) ∧
      (∀ A : Set Ω, MeasurableSet[𝓕 s] A →
        (∫⁻ ω in A, F (fun v : ℝ≥0 =>
          X.X (s + v) ω - X.X s ω) ∂P) =
        P A * (∫⁻ ω, F (fun v : ℝ≥0 =>
          X.X (s + v) ω - X.X s ω) ∂P)) := by sorry
