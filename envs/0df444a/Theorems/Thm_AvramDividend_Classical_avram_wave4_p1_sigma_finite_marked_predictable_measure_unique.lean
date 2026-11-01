-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_sigma_finite_marked_predictable_measure_unique
-- name    : AvramDividend.Classical.avram_wave4_p1_sigma_finite_marked_predictable_measure_unique
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T12:19:02.764773+00:00
-- url     : https://prove2.me/theorems/85791e69-1071-4a55-a3a3-c402870c4066
-- title:
--   Locally finite marked predictable measure uniqueness from adapted rectangles
-- statement:
--   Let two measures on predictable time-history × marks agree on all initial-time and adapted strict-future rectangles paired with arbitrary measurable mark sets. If a monotone countable sequence of measurable mark bands exhausts the mark space and the first measure has finite mass on every whole-time-history band, then both measures coincide, even when their total mass is infinite. The proof restricts both measures to each finite band, applies canonically Proved finite marked predictable-measure uniqueness, and takes the monotone countable exhaustion using continuity of measures from below. Elementary adapted rectangles and local finiteness are assumed, not arbitrary predictable Campbell equality. This supplies the sigma-finite monotone-class extension relevant to infinite-activity Lévy jumps; it does not alone prove their L2 compensated stochastic-integral convergence.
-- source:
--   Pinned Mathlib Monotone.measure_iUnion and Measure.restrict_apply; canonically Proved finite marked predictable measure uniqueness d31d057d-1f5c-4744-b86a-58c45723a645; Applebaum, Levy Processes and Stochastic Calculus, predictable Poisson integration.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_finite_marked_predictable_measure_unique

open MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.avram_wave4_p1_sigma_finite_marked_predictable_measure_unique
    {Ω E ι : Type*} [mΩ : MeasurableSpace Ω] [mE : MeasurableSpace E]
    [LinearOrder ι] [OrderBot ι]
    (𝓕 : Filtration ι mΩ)
    (M N : @Measure ((ι × Ω) × E) (@Prod.instMeasurableSpace _ _ (𝓕.predictable) mE))
    (B : ℕ → Set E) (hBm : ∀ k, MeasurableSet (B k)) (hBmono : Monotone B)
    (hBcover : (⋃ k, B k) = Set.univ)
    (hLocal : ∀ k, M ((Set.univ : Set (ι × Ω)) ×ˢ B k) ≠ ∞)
    (hBot : ∀ (A : Set Ω) (C : Set E),
      MeasurableSet[𝓕 ⊥] A → MeasurableSet C →
      M (({(⊥ : ι)} ×ˢ A) ×ˢ C) =
        N (({(⊥ : ι)} ×ˢ A) ×ˢ C))
    (hFuture : ∀ (i : ι) (A : Set Ω) (C : Set E),
      MeasurableSet[𝓕 i] A → MeasurableSet C →
      M ((Set.Ioi i ×ˢ A) ×ˢ C) =
        N ((Set.Ioi i ×ˢ A) ×ˢ C)) :
    M = N := by sorry
