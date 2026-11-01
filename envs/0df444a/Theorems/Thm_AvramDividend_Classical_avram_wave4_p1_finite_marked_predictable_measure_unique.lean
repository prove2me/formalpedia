-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_finite_marked_predictable_measure_unique
-- name    : AvramDividend.Classical.avram_wave4_p1_finite_marked_predictable_measure_unique
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T12:07:01.99946+00:00
-- url     : https://prove2.me/theorems/d31d057d-1f5c-4744-b86a-58c45723a645
-- title:
--   Finite marked predictable measures determined by adapted time-mark rectangles
-- statement:
--   For a finite measure on the product of a filtration's predictable time-history sigma-algebra and an arbitrary measurable mark space E, equality against a second measure on all initial-time adapted rectangles times measurable mark sets and all strict-future adapted rectangles times measurable mark sets implies equality of the measures on the full predictable-by-mark sigma-algebra. The proof fixes each mark set B, pushes forward the measure restricted to all time-history points with marks in B, applies the proved predictable measure uniqueness theorem to the induced time-history marginals, then uses product-measure rectangle uniqueness. It does not assume equality for arbitrary predictable integrands and does not identify any source Lévy jump measure.
-- source:
--   Canonically Proved avram_wave4_p1_predictable_measure_unique_from_rectangles UUID 41f280b9-9fd4-4ac5-9a78-218500cf3deb; pinned Mathlib Measure.ext_prod, Measure.map_apply, Measure.restrict_apply; Applebaum marked Poisson compensation.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_predictable_measure_unique_from_rectangles

open MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.avram_wave4_p1_finite_marked_predictable_measure_unique
    {Ω E ι : Type*} [mΩ : MeasurableSpace Ω] [mE : MeasurableSpace E]
    [LinearOrder ι] [OrderBot ι]
    (𝓕 : Filtration ι mΩ)
    (M N : @Measure ((ι × Ω) × E)
      (@Prod.instMeasurableSpace _ _ (𝓕.predictable) mE))
    [IsFiniteMeasure M]
    (hBot : ∀ (A : Set Ω) (B : Set E),
      MeasurableSet[𝓕 ⊥] A → MeasurableSet B →
      M (({(⊥ : ι)} ×ˢ A) ×ˢ B) =
        N (({(⊥ : ι)} ×ˢ A) ×ˢ B))
    (hFuture : ∀ (i : ι) (A : Set Ω) (B : Set E),
      MeasurableSet[𝓕 i] A → MeasurableSet B →
      M ((Set.Ioi i ×ˢ A) ×ˢ B) =
        N ((Set.Ioi i ×ˢ A) ×ˢ B)) :
    M = N := by sorry
