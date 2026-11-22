-- Prove2me | solution 1 for vcdim_finite_imp_pac
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:43:44.858741+00:00
-- url     : https://prove2.me/submissions/8db1ab35-4a92-41f3-b1e1-378e3f426223

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Compression
public import Definitions.Def_LeanPool_FormalLearningTheory_Bridge
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Measurability
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_GeneralizationResults
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Theorem_PAC
public import Theorems.Thm_MeasurableConceptClass_hWB
public import Theorems.Thm_MeasurableConceptClass_hc_meas
public import Theorems.Thm_P2M_vcdim_finite_imp_uc__685a2436ce92
public import Theorems.Thm_uc_imp_pac


set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) (hC : VCDim X C < ⊤)
    [MeasurableConceptClass X C] :
    PACLearnable X C := by
  have hmeas_C := MeasurableConceptClass.hmeas_C C
  have hc_meas := MeasurableConceptClass.hc_meas C
  have hWB := MeasurableConceptClass.hWB C
  -- Route through UC path in Symmetrization.lean:
  -- vcdim_finite_imp_uc' + uc_imp_pac.
  by_cases hne : C.Nonempty
  · exact uc_imp_pac X C hne (vcdim_finite_imp_uc' X C hC hmeas_C hc_meas hWB)
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    exact ⟨⟨Set.univ, fun _ => fun _ => false, fun _ => Set.mem_univ _⟩,
           fun _ _ => 0, fun _ _ _ _ _ _ c hcC => by simp [hne] at hcC⟩
