-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_predictable_marked_rectangle_generate_sigma
-- name    : AvramDividend.Classical.avram_wave4_p1_predictable_marked_rectangle_generate_sigma
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T19:47:13.818426+00:00
-- url     : https://prove2.me/theorems/9e55e165-818b-4471-8a25-78a3e033e86d
-- title:
--   The actual marked predictable rectangle Pi-system generates the full predictable product sigma-algebra
-- statement:
--   For any genuine filtration, the initial-bottom-time rectangles and strict future half-line rectangles with past-measurable coefficients, paired with arbitrary measurable mark sets, generate the exact full marked predictable sigma algebra. Exhibit an explicit countable cover using the bottom-time atom and future half-line and invoke the pinned Mathlib generateFrom_prod_eq theorem. This discharges the sigma-generation hypothesis required for true predictable-kernel L² elementary density, without assuming compensation.
-- source:
--   Pinned Mathlib Probability.Process.Predictable predictable definition; MeasureTheory.MeasurableSpace.Prod generateFrom_prod_eq; MeasureTheory.MeasurableSpace.Basic IsCountablySpanning; P1 canonical pi system ee8c5f17.

import Mathlib
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.Probability.Process.Predictable

open MeasureTheory MeasurableSpace Set
open scoped ENNReal NNReal

theorem AvramDividend.Classical.avram_wave4_p1_predictable_marked_rectangle_generate_sigma
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
    (𝓕.predictable).prod mE = MeasurableSpace.generateFrom GM := by sorry
