-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_original_filtration_marked_finite_band_l2_dense
-- name    : AvramDividend.Classical.avram_wave4_p1_original_filtration_marked_finite_band_l2_dense
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T20:08:34.822322+00:00
-- url     : https://prove2.me/theorems/a44fb480-7fcb-4bde-9fe7-8b82c4ac97e3
-- title:
--   Actual-filtration marked predictable finite-band step-kernel span is dense in L²
-- statement:
--   For the genuine original filtration and its marked predictable product measurable space, any finite energy measure has dense L² span of original adapted past-event × future-time × measurable-mark rectangles (adjoining the universe and empty set). Apply the verified original Pi-system theorem, exact marked sigma-generation theorem, and independent finite-measure Pi indicator L² density. This removes all separate structural Pi/density hypotheses at the source-X application boundary, but does not assume or prove Lévy jump intensity or compensated stochastic isometry.
-- source:
--   Canonical P1 imports ee8c5f17 Pi, 9e55e165 marked sigma-generation (pending proof), 7a68dc8d full finite-measure L² Pi density (pending proof).

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_predictable_marked_rectangle_pi_system
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_predictable_marked_rectangle_generate_sigma
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_pi_generator_l2_dense_after_lift

open MeasureTheory MeasurableSpace Set AvramDividend.Classical
open scoped ENNReal NNReal

theorem AvramDividend.Classical.avram_wave4_p1_original_filtration_marked_finite_band_l2_dense
    {Ω ι E : Type*} [mΩ : MeasurableSpace Ω]
    [LinearOrder ι] [OrderBot ι] [mE : MeasurableSpace E]
    (𝓕 : Filtration ι mΩ)
    [mAll : MeasurableSpace ((ι × Ω) × E)]
    (μ : Measure ((ι × Ω) × E)) [IsFiniteMeasure μ]
    (hAll : mAll = (𝓕.predictable).prod mE) :
    let G : Set (Set (ι × Ω)) :=
      {S | (∃ A : Set Ω, MeasurableSet[𝓕 ⊥] A ∧
                S = ({⊥} ×ˢ A)) ∨
           (∃ i : ι, ∃ A : Set Ω, MeasurableSet[𝓕 i] A ∧
                S = (Set.Ioi i ×ˢ A))}
    let GM : Set (Set ((ι × Ω) × E)) :=
      Set.image2 (· ×ˢ ·) G {C : Set E | MeasurableSet C}
    let GP : Set (Set ((ι × Ω) × E)) :=
      insert Set.univ (insert (∅ : Set ((ι × Ω) × E)) GM)
    let S : Set (Lp ℝ (2 : ℝ≥0∞) μ) :=
      {v | ∃ (t : Set ((ι × Ω) × E)) (ht : t ∈ GP)
        (htm : MeasurableSet t) (hμt : μ t ≠ ⊤),
        indicatorConstLp (2 : ℝ≥0∞) htm hμt (1 : ℝ) = v}
    ∀ f : Lp ℝ (2 : ℝ≥0∞) μ,
      f ∈ (Submodule.span ℝ S).topologicalClosure := by sorry
