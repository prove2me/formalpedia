-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_original_past_kernel_all_real_source_rate
-- name    : AvramDividend.Classical.avram_p2_d_future_original_past_kernel_all_real_source_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:45:05.419096+00:00
-- url     : https://prove2.me/theorems/f2a8ef2f-f309-46de-874d-831bd6eeecb7
-- title:
--   Original future extractor has all-real conditional past-event source-count rate
-- statement:
--   For the original P, filtration and spectrally negative Lévy process, there is one measurable future marked-count functional with exact pathwise evaluation and past-event expectation P(A) times (t-s) times the original unit-time source count mean, at every real ordered horizon. The scalar rate is count-derived and is not asserted equal to X.ν.
-- source:
--   Proved P2-D source future extractor and exact past kernel aa898276; substitute Proved original all-real zero-origin source rate.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_original_past_kernel_zero_origin_mean
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_original_zero_origin_all_real_source_rate

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_original_past_kernel_all_real_source_rate
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
      ∀ (A : Set Ω), MeasurableSet[𝓕 s] A →
        (∫⁻ ω in A, F (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω) ∂P) =
          P A * (((t - s : ℝ≥0) : ℝ≥0∞) * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 (1 : ℝ≥0) ×ˢ B) ∂P)) := by sorry
