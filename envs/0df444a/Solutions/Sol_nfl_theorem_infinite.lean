-- Prove2me | solution 1 for nfl_theorem_infinite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:44:45.087419+00:00
-- url     : https://prove2.me/submissions/428e91c1-9ad5-4794-8e0c-38acd03fd0c0

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
public import Theorems.Thm_pac_imp_vcdim_finite
public import Theorems.Thm_vcdim_univ_infinite

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution (X : Type u) [MeasurableSpace X]
    [MeasurableSingletonClass X] [Infinite X] :
    ¬ PACLearnable X (Set.univ : ConceptClass X Bool) := by
  intro h
  have hfin := pac_imp_vcdim_finite X (Set.univ : ConceptClass X Bool) h
  rw [vcdim_univ_infinite] at hfin
  exact lt_irrefl _ hfin
