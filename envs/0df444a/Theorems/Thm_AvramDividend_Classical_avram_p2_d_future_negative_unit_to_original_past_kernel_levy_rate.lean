-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_negative_unit_to_original_past_kernel_levy_rate
-- name    : AvramDividend.Classical.avram_p2_d_future_negative_unit_to_original_past_kernel_levy_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:42:05.120204+00:00
-- url     : https://prove2.me/theorems/27fdb8c9-3db3-4f0e-a43a-f4d29725dd01
-- title:
--   Negative unit-time Lévy identification gives the genuine future kernel and all past-event arbitrary Borel rates
-- statement:
--   Assuming only the explicit original unit-time jump mean identification with the triplet Lévy measure on strictly negative Borel sets, obtain for every arbitrary Borel mark set and real future interval an exact original-process future-increment measurable extractor and past-event expectation P(A)(t-s)X.ν(B). This is the complete source-exact P2-E kernel interface conditional on the one unresolved genuine Lévy–Itô unit identity, without replacing the original process.
-- source:
--   Proved negative-unit to all-Borel source rate af526de8 at (0,1) gives the original arbitrary-B unit-time count identity; Proved original all-real source future extractor/past kernel f2a8ef2f then rewrites the rate.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_original_past_kernel_all_real_source_rate
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_negative_unit_mean_to_arbitrary_borel_rate

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_negative_unit_to_original_past_kernel_levy_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hunitNegative : ∀ (C : Set ℝ), MeasurableSet C →
      C ⊆ Iio (0 : ℝ) → (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 (1 : ℝ≥0) ×ˢ C) ∂P) = X.ν C) :
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
          P A * (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) := by sorry
