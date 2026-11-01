-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_predictable_marked_rectangle_pi_system
-- name    : AvramDividend.Classical.avram_wave4_p1_predictable_marked_rectangle_pi_system
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T18:41:03.409545+00:00
-- url     : https://prove2.me/theorems/ee8c5f17-2bf6-4919-b5b8-4d6687e8175f
-- title:
--   Actual-filtration marked predictable adapted rectangles form a Pi-system
-- statement:
--   Show the genuine filtration-adapted predictable time generator of initial bottom-time atoms and strictly future half-lines with coefficients measurable at their lower endpoints is closed under nonempty intersections. In a mixed initial/future case the intersection is empty; in two future cases choose the later left endpoint and promote the earlier coefficient through filtration monotonicity; in the initial case intersect past-measurable events. Then Mathlib IsPiSystem.prod and isPiSystem_measurableSet prove the marked-product generator is a Pi-system. This supplies a genuinely unproved finite-intersection mathematical step needed for Boolean-algebra/simple marked predictable tensor reduction and a pi-lambda extension. No Poisson law, compensation, stochastic isometry or martingale conclusion is assumed.
-- source:
--   Pinned Mathlib Probability.Process.Filtration Filtration.mono and MeasureTheory.PiSystem IsPiSystem.prod; Set.prod_inter_prod and interval order comparison. Independent of all other P1 newly authored imports.

import Mathlib

open MeasureTheory MeasurableSpace Set
open scoped ENNReal NNReal

theorem AvramDividend.Classical.avram_wave4_p1_predictable_marked_rectangle_pi_system
    {Ω ι E : Type*} [mΩ : MeasurableSpace Ω]
    [LinearOrder ι] [OrderBot ι] [mE : MeasurableSpace E]
    (𝓕 : Filtration ι mΩ) :
    let G : Set (Set (ι × Ω)) :=
      {S | (∃ A : Set Ω, MeasurableSet[𝓕 ⊥] A ∧
                S = ({⊥} ×ˢ A)) ∨
           (∃ i : ι, ∃ A : Set Ω, MeasurableSet[𝓕 i] A ∧
                S = (Set.Ioi i ×ˢ A))}
    let GM : Set (Set ((ι × Ω) × E)) :=
      Set.image2 (· ×ˢ ·) G {C : Set E | MeasurableSet C}
    IsPiSystem G ∧ IsPiSystem GM := by sorry
