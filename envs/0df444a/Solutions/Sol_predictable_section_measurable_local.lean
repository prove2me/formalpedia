-- Prove2me | solution 1 for predictable_section_measurable_local
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T09:46:12.875107+00:00
-- url     : https://prove2.me/submissions/02c5b243-31b7-405e-aa72-93368355709a

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

noncomputable section
theorem predictable_section_measurable_local
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 mΩ) (ω : Ω) :
    @Measurable ℝ≥0 (ℝ≥0 × Ω) inferInstance 𝓕.predictable (fun t => (t, ω)) := by
  unfold MeasureTheory.Filtration.predictable
  apply measurable_generateFrom
  rintro s (⟨A, _, rfl⟩ | ⟨i, A, _, rfl⟩)
  · by_cases hω : ω ∈ A
    · have h : (fun t : ℝ≥0 => (t, ω)) ⁻¹' ({⊥} ×ˢ A) = {⊥} := by ext t; simp [hω]
      rw [h]; exact measurableSet_singleton _
    · have h : (fun t : ℝ≥0 => (t, ω)) ⁻¹' ({⊥} ×ˢ A) = ∅ := by ext t; simp [hω]
      rw [h]; exact MeasurableSet.empty
  · by_cases hω : ω ∈ A
    · have h : (fun t : ℝ≥0 => (t, ω)) ⁻¹' (Set.Ioi i ×ˢ A) = Set.Ioi i := by ext t; simp [hω]
      rw [h]; exact measurableSet_Ioi
    · have h : (fun t : ℝ≥0 => (t, ω)) ⁻¹' (Set.Ioi i ×ˢ A) = ∅ := by ext t; simp [hω]
      rw [h]; exact MeasurableSet.empty

theorem solution
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 mΩ) (ω : Ω) :
    @Measurable ℝ≥0 (ℝ≥0 × Ω) inferInstance 𝓕.predictable (fun t => (t, ω)) := by
  unfold MeasureTheory.Filtration.predictable
  apply measurable_generateFrom
  rintro s (⟨A, _, rfl⟩ | ⟨i, A, _, rfl⟩)
  · by_cases hω : ω ∈ A
    · have h : (fun t : ℝ≥0 => (t, ω)) ⁻¹' ({⊥} ×ˢ A) = {⊥} := by ext t; simp [hω]
      rw [h]; exact measurableSet_singleton _
    · have h : (fun t : ℝ≥0 => (t, ω)) ⁻¹' ({⊥} ×ˢ A) = ∅ := by ext t; simp [hω]
      rw [h]; exact MeasurableSet.empty
  · by_cases hω : ω ∈ A
    · have h : (fun t : ℝ≥0 => (t, ω)) ⁻¹' (Set.Ioi i ×ˢ A) = Set.Ioi i := by ext t; simp [hω]
      rw [h]; exact measurableSet_Ioi
    · have h : (fun t : ℝ≥0 => (t, ω)) ⁻¹' (Set.Ioi i ×ˢ A) = ∅ := by ext t; simp [hω]
      rw [h]; exact MeasurableSet.empty

end

