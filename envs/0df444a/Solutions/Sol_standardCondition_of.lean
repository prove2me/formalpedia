-- Prove2me | solution 1 for standardCondition_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:39:49.780669+00:00
-- url     : https://prove2.me/submissions/9310f8ee-0609-452f-9224-88cd5c5df4f6

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Measure.Real
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Definitions.Def_Polychromatic_LocalLemma
import Theorems.Thm_indepFrom_iff_indepSets
import Theorems.Thm_eq_sInter_of_mem_generatePiSystem
import Theorems.Thm_dependsOn_mem_iff_exists_preimage
import Theorems.Thm_MeasurableSet_of_restrict_preimage


set_option autoImplicit true
open MeasureTheory ProbabilityTheory Measure
variable {ι Ω : Type*} {hΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {A : ι → Set Ω} {N : ι → Finset ι} {x : ι → ℝ} {i j : ι} {S T : Finset ι}
open Finset
theorem _root_.solution {α β : Type*} [Finite ι] [MeasurableSpace β] [IsProbabilityMeasure P]
    (I : α → Ω → β) {A : ι → Set Ω} {N : ι → Finset ι} (D : ι → Finset α)
    (hND : ∀ i j, i ≠ j → i ∉ N j → Disjoint (D i) (D j))
    (hI : ∀ a : α, Measurable (I a))
    (hI' : iIndepFun I P)
    (hA : ∀ i, ∃ S : Set (α → β), MeasurableSet S ∧
      DependsOn (· ∈ S) (D i) ∧ A i = (fun ω a ↦ I a ω) ⁻¹' S) :
    standardCondition P A N := by
  have := Fintype.ofFinite ι
  rw [standardCondition]
  have hA' (i : ι) : MeasurableSet (A i) := by
    obtain ⟨S, hS, -, h⟩ := hA i
    rw [h]
    exact MeasurableSet.preimage hS (by fun_prop)
  intro i
  rw [indepFrom_iff_indepSets (hA' _) (by grind), IndepSets_iff]
  intro X₁ X₂ hX₁ hX₂
  cases hX₁
  replace hX₂ := eq_sInter_of_mem_generatePiSystem hX₂
  simp only [Set.exists_subset_image_iff, Set.sInter_image,
    Set.subset_compl_iff_disjoint_right, Set.disjoint_insert_right] at hX₂
  obtain ⟨J, ⟨hiJ, hJ⟩, rfl⟩ := hX₂
  obtain ⟨Si, hSi, hSDi, hAi⟩ := hA i
  have hAj' : MeasurableSet (⋂ j ∈ J, A j) := by
    apply MeasurableSet.biInter (Set.to_countable _)
    simp [hA']
  lift J to Finset ι using Set.toFinite _
  simp only [SetLike.mem_coe, disjoint_coe] at hiJ hJ hAj' ⊢
  classical
  obtain ⟨Sj, hSj, hSDj, hAj⟩ :
      ∃ Sj : Set (α → β), MeasurableSet Sj ∧ DependsOn (· ∈ Sj) (J.biUnion D) ∧
        (⋂ j ∈ J, A j) = (fun ω a ↦ I a ω) ⁻¹' Sj := by
    choose S hSm hSd hSA using hA
    refine ⟨⋂ j ∈ J, S j, MeasurableSet.biInter (Set.to_countable _) (by simp [hSm]), ?_, ?_⟩
    · simp [DependsOn] at hSd ⊢
      grind
    · simp [Set.preimage_iInter₂, hSA]
  rw [hAi, hAj]
  obtain rfl | hi := Si.eq_empty_or_nonempty
  · simp
  obtain rfl | hj := Sj.eq_empty_or_nonempty
  · simp
  obtain ⟨Si, rfl⟩ := dependsOn_mem_iff_exists_preimage.1 hSDi
  obtain ⟨Sj, rfl⟩ := dependsOn_mem_iff_exists_preimage.1 hSDj
  clear hSDi hSDj
  rw [← Set.preimage_comp, ← Set.preimage_comp]
  refine IndepFun.measure_inter_preimage_eq_mul (hI'.indepFun_finset _ _ ?_ hI) _ _
    (.of_restrict_preimage hi hSi) (.of_restrict_preimage hj hSj)
  rw [Finset.disjoint_biUnion_right]
  intro j hj
  exact (hND _ _ (by grind) (hJ.notMem_of_mem_left_finset hj)).symm
