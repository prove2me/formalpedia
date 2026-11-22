-- Prove2me | solution 1 for pac_imp_vcdim_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:36:43.107942+00:00
-- url     : https://prove2.me/submissions/56b32a57-097c-4351-9b6a-7fce617f67e3

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
public import Theorems.Thm_vcdim_infinite_not_pac


set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution (X : Type u) [MeasurableSpace X]
    [MeasurableSingletonClass X]
    (C : ConceptClass X Bool) (hC : PACLearnable X C) :
    VCDim X C < ⊤ := by
  -- M-Contrapositive: VCDim = ⊤ → ¬PACLearnable (in Generalization.lean)
  by_contra h
  exact absurd hC (vcdim_infinite_not_pac X C (le_antisymm le_top (not_lt.mp h)))
