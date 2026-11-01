-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_predictable_marked_rectangle_algebra_measure_dense
-- name    : AvramDividend.Classical.avram_wave4_p1_predictable_marked_rectangle_algebra_measure_dense
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T18:11:46.795796+00:00
-- url     : https://prove2.me/theorems/eeb18b8e-71e6-46c8-a22a-fda695317aa9
-- title:
--   Finite marked predictable measure density of adapted time-history × mark rectangles
-- statement:
--   On the actual predictable time-history × mark measurable space of an arbitrary filtration and mark measurable space, every finite measure admits set-algebra approximation by finite Boolean combinations of genuinely adapted past-time and measurable-mark rectangles. Derive this from a separately proved marked-product generator identity and pinned Mathlib finite-measure set-algebra density. Does not assume Campbell, martingale, compensator or source Lévy PRM law; supports the finite-band predictable marked L² approximation bridge.
-- source:
--   Imports canonical P1 marked product predictable generator (new authoring job 8c3c3cd3-b9cf-4105-856d-3047ed908e14, wait until Proved); pinned MeasureDense.of_generateFrom_isSetAlgebra_finite, generateFrom_generateSetAlgebra_eq.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_predictable_marked_product_rectangle_generator

open MeasureTheory MeasurableSpace Set AvramDividend.Classical
open scoped ENNReal NNReal

theorem AvramDividend.Classical.avram_wave4_p1_predictable_marked_rectangle_algebra_measure_dense
    {Ω ι E : Type*} [mΩ : MeasurableSpace Ω]
    [LinearOrder ι] [OrderBot ι] [mE : MeasurableSpace E]
    (𝓕 : Filtration ι mΩ)
    [mHist : MeasurableSpace (ι × Ω)]
    (hHist : mHist = 𝓕.predictable)
    [mMarked : MeasurableSpace ((ι × Ω) × E)]
    (hMarked : mMarked = @Prod.instMeasurableSpace (ι × Ω) E mHist mE)
    (μ : Measure ((ι × Ω) × E)) [IsFiniteMeasure μ] :
    let G : Set (Set (ι × Ω)) :=
      {S | (∃ A : Set Ω, MeasurableSet[𝓕 ⊥] A ∧
                S = ({⊥} ×ˢ A)) ∨
           (∃ i : ι, ∃ A : Set Ω, MeasurableSet[𝓕 i] A ∧
                S = (Set.Ioi i ×ˢ A))}
    let GM : Set (Set ((ι × Ω) × E)) :=
      Set.image2 (· ×ˢ ·) G {C : Set E | MeasurableSet C}
    μ.MeasureDense (generateSetAlgebra GM) := by sorry
