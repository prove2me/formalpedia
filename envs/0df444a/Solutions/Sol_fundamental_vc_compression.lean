-- Prove2me | solution 1 for fundamental_vc_compression
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:47:54.492526+00:00
-- url     : https://prove2.me/submissions/84d83e2e-5347-4c31-89a5-6a7e613e240d

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
public import Theorems.Thm_fundamental_vc_compression_with_info


set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution (X : Type u)
    (C : ConceptClass X Bool) :
    (VCDim X C < ⊤) ↔
    (∃ (k : ℕ) (cs : CompressionSchemeWithInfo0 X Bool C), cs.size = k) :=
  fundamental_vc_compression_with_info X C
