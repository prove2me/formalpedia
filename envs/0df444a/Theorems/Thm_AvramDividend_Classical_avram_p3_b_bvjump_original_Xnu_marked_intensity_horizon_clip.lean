-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_Xnu_marked_intensity_horizon_clip
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_Xnu_marked_intensity_horizon_clip
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:50:06.959194+00:00
-- url     : https://prove2.me/theorems/ff889647-e0ff-4c96-b69b-837d000c52ff
-- title:
--   Original marked Lévy predictable intensity clips arbitrary adapted cells at true physical horizon
-- statement:
--   For the actual original source Lévy X on Ω/P/rightCont filtration and canonical finite predictable physical clock μ, the marked intensity N=μ.prod(X.ν restricted to negative) gives exactly the same mass to any adapted (s,t]×A×B as the interval clipped at min(t,T). No ordering condition on s,t,T, and zero-infinite mark intensities are handled by ENNReal algebra without cancellation. This supplies crossing-horizon marked-intensity compatibility for P3's original source future extractor.
-- source:
--   Proved P3-B actual X.ν product intensity and physical clock clipped mass; original predictable adapted rectangles.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_Xnu_physical_intensity_cell
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_clock_interval_mass_clipped
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_Xnu_marked_intensity_horizon_clip
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμclock : ∀ E : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] E →
      μ E = ((((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) E)
    (N : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (hN : N = (letI : MeasurableSpace (ℝ≥0 × Ω) :=
      𝓕.rightCont.predictable;
      μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
    (s t : ℝ≥0)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) :
    N ((Ioc s t ×ˢ A) ×ˢ B) =
      N ((Ioc s (min t T) ×ˢ A) ×ˢ B) := by sorry
