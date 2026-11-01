-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_predictable_marked_l2_dense_adapted_boolean_indicator_span
-- name    : AvramDividend.Classical.avram_wave4_p1_predictable_marked_l2_dense_adapted_boolean_indicator_span
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T18:22:52.31776+00:00
-- url     : https://prove2.me/theorems/46c918bc-371d-438f-84bf-d825c3aad9f8
-- title:
--   Full L² density of original-filtration marked predictable adapted Boolean indicator spans
-- statement:
--   For every finite measure on the genuine predictable time-history × arbitrary mark measurable space of an original filtration, prove full L² density of the real linear span of indicators of finite Boolean combinations of past-adapted marked rectangles. Use the separately proved marked-product generator and marked Boolean measure-density, then pinned Mathlib MeasureDense indicator closure, Submodule span topological closure, and Lp.induction; no Poisson compensation or isometry conclusion is assumed. This is a rigorous nonstochastic predictable marked-kernel approximation interface; conversion to finite deterministic grid cells and the same-X stochastic isometry extension are additional steps.
-- source:
--   Dependent on P1 marked Boolean measure-density theorem not yet published; defer authoring until its parent is canonical Proved. Pinned Mathlib SeparableMeasure, SimpleFuncDenseLp and Submodule topologicalClosure.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_predictable_marked_rectangle_algebra_measure_dense

open MeasureTheory MeasurableSpace Set TopologicalSpace AvramDividend.Classical
open scoped ENNReal NNReal

theorem AvramDividend.Classical.avram_wave4_p1_predictable_marked_l2_dense_adapted_boolean_indicator_span
    {Ω ι E : Type*} [mΩ : MeasurableSpace Ω]
    [LinearOrder ι] [OrderBot ι] [mE : MeasurableSpace E]
    (𝓕 : Filtration ι mΩ)
    [mHist : MeasurableSpace (ι × Ω)]
    (hHist : mHist = 𝓕.predictable)
    [mMarked : MeasurableSpace ((ι × Ω) × E)]
    (hMarked : mMarked = @Prod.instMeasurableSpace (ι × Ω) E mHist mE)
    (μ : Measure ((ι × Ω) × E)) [IsFiniteMeasure μ] :
    let G : Set (Set (ι × Ω)) :=
      {T | (∃ A : Set Ω, MeasurableSet[𝓕 ⊥] A ∧
                T = ({⊥} ×ˢ A)) ∨
           (∃ i : ι, ∃ A : Set Ω, MeasurableSet[𝓕 i] A ∧
                T = (Set.Ioi i ×ˢ A))}
    let GM : Set (Set ((ι × Ω) × E)) :=
      Set.image2 (· ×ˢ ·) G {C : Set E | MeasurableSet C}
    let hGM : μ.MeasureDense (generateSetAlgebra GM) :=
      avram_wave4_p1_predictable_marked_rectangle_algebra_measure_dense
        𝓕 hHist hMarked μ
    let S : Set (Lp ℝ (2 : ℝ≥0∞) μ) :=
      {v | ∃ (t : Set ((ι × Ω) × E)) (ht : t ∈ generateSetAlgebra GM)
        (hμt : μ t ≠ ⊤) (c : ℝ),
        indicatorConstLp (2 : ℝ≥0∞) (hGM.measurable t ht) hμt c = v}
    ∀ f : Lp ℝ (2 : ℝ≥0∞) μ,
      f ∈ (Submodule.span ℝ S).topologicalClosure := by sorry
