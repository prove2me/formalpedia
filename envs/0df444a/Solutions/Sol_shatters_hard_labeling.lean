-- Prove2me | solution 1 for shatters_hard_labeling
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:43:47.743615+00:00
-- url     : https://prove2.me/submissions/110d5155-f6e0-47a7-9683-369c2b1a49d0

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_VCDimension
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_PAC
public import Mathlib.Probability.Independence.Basic
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Probability.ProductMeasure
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Tail
public import Theorems.Thm_shatters_realize
public import Theorems.Thm_exists_many_disagreements


set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution {X : Type u} {C : ConceptClass X Bool} {T : Finset X}
    (hT : Shatters X C T) (h : ↥T → Bool) (hcard : 2 ≤ T.card) :
    ∃ c ∈ C, T.card <
      4 * (Finset.univ.filter fun x : ↥T => c (x : X) ≠ h x).card := by
  classical
  have hcard' : 2 ≤ Fintype.card ↥T := by rwa [Fintype.card_coe]
  obtain ⟨f, hf⟩ := exists_many_disagreements h hcard'
  obtain ⟨c, hcC, hcf⟩ := shatters_realize hT f
  refine ⟨c, hcC, ?_⟩
  simp_all
