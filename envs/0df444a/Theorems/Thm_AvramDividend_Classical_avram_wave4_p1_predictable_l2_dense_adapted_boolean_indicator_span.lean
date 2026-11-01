-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_predictable_l2_dense_adapted_boolean_indicator_span
-- name    : AvramDividend.Classical.avram_wave4_p1_predictable_l2_dense_adapted_boolean_indicator_span
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T18:03:18.831181+00:00
-- url     : https://prove2.me/theorems/279665b5-13df-4f0d-b8b3-a0ef615d4858
-- title:
--   Full L² density of the adapted predictable Boolean-indicator linear span
-- statement:
--   For the actual predictable sigma algebra of an arbitrary filtration with any finite measure, every real L² class lies in the norm closure of the finite real linear span of constant indicators of Boolean combinations of genuine adapted past-time rectangles. This is a full infinite-dimensional L² density theorem, not just indicator density. Derive it noncircularly using the already Proved adapted-algebra MeasureDense theorem, the pinned MeasureDense.indicatorConstLp_subset_closure, Submodule span's topological closure, and pinned Lp.induction on indicators and addition. There is no stochastic compensation or martingale assumption.
-- source:
--   P1 canonical adapted Boolean MeasureDense d1cdf93e-bb12-45f4-a758-8a3fcc710a03; pinned Mathlib SeparableMeasure, SimpleFuncDenseLp Lp.induction, Submodule.closure_subset_topologicalClosure_span.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_predictable_generator_set_algebra_measure_dense

open MeasureTheory Set TopologicalSpace AvramDividend.Classical
open scoped ENNReal NNReal

theorem AvramDividend.Classical.avram_wave4_p1_predictable_l2_dense_adapted_boolean_indicator_span
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    [LinearOrder ι] [OrderBot ι]
    (𝓕 : Filtration ι mΩ)
    [mProd : MeasurableSpace (ι × Ω)]
    (hProd : mProd = 𝓕.predictable)
    (μ : Measure (ι × Ω)) [IsFiniteMeasure μ] :
    let G : Set (Set (ι × Ω)) :=
      {T | (∃ A : Set Ω, MeasurableSet[𝓕 ⊥] A ∧
                T = ({⊥} ×ˢ A)) ∨
           (∃ i : ι, ∃ A : Set Ω, MeasurableSet[𝓕 i] A ∧
                T = (Set.Ioi i ×ˢ A))}
    let hG : μ.MeasureDense (generateSetAlgebra G) :=
      avram_wave4_p1_predictable_generator_set_algebra_measure_dense 𝓕 hProd μ
    let S : Set (Lp ℝ (2 : ℝ≥0∞) μ) :=
      {v | ∃ (t : Set (ι × Ω)) (ht : t ∈ generateSetAlgebra G)
        (hμt : μ t ≠ ⊤) (c : ℝ),
        indicatorConstLp (2 : ℝ≥0∞) (hG.measurable t ht) hμt c = v}
    ∀ f : Lp ℝ (2 : ℝ≥0∞) μ,
      f ∈ (Submodule.span ℝ S).topologicalClosure := by sorry
