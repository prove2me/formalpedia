-- Prove2me | solution 1 for fundamental_vc_compression_with_info
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:46:27.946112+00:00
-- url     : https://prove2.me/submissions/56090051-c5b5-4881-b063-2a6f5d861823

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_FiniteVCApprox
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Tail
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_FiniteSupportUC
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Compression
public import Theorems.Thm_vcdim_finite_imp_compression_with_info
public import Theorems.Thm_compression_with_info_imp_vcdim_finite

set_option autoImplicit true
@[expose] public section
public section
open Finset
noncomputable section
universe u
attribute [local instance] Classical.propDecidable
theorem _root_.solution
    (X : Type u) (C : ConceptClass X Bool) :
    (VCDim X C < ⊤) ↔
    (∃ (k : ℕ) (cs : CompressionSchemeWithInfo0 X Bool C), cs.size = k) :=
  ⟨vcdim_finite_imp_compression_with_info X C,
   fun ⟨k, cs, hk⟩ => compression_with_info_imp_vcdim_finite X C ⟨k, cs, hk⟩⟩
