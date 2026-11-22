-- Prove2me | solution 1 for vcdim_eq_finset_vcdim
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:39:48.502062+00:00
-- url     : https://prove2.me/submissions/16c8227d-6f6f-4b0f-8187-84413c8464e6

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Data
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Ordinal
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_Bayesian
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Bridge
public import Theorems.Thm_shatters_iff_finset_shatters

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution {X : Type u} [Fintype X] [DecidableEq X]
    (C : Finset (X → Bool)) :
    VCDim X (↑C : Set (X → Bool)) = ↑(Finset.vcDim (conceptClassToFinsetFamily C)) := by
  let 𝒜 := conceptClassToFinsetFamily C
  apply le_antisymm
  · -- VCDim ≤ ↑(Finset.vcDim 𝒜)
    -- Suffices to show: for each S with Shatters X ↑C S, S.card ≤ Finset.vcDim 𝒜
    apply iSup_le; intro S
    apply iSup_le; intro hS
    -- Convert: Shatters X ↑C S → 𝒜.Shatters S
    have hS' : 𝒜.Shatters S := (shatters_iff_finset_shatters C S).mp hS
    -- Mathlib: Shatters.card_le_vcDim
    exact WithTop.coe_le_coe.mpr hS'.card_le_vcDim
  · -- ↑(Finset.vcDim 𝒜) ≤ VCDim
    -- Strategy: show ↑n ≤ iSup where n = 𝒜.shatterer.sup card
    -- For each S ∈ 𝒜.shatterer, S.card ≤ n, and Shatters X ↑C S holds
    -- So if shatterer is nonempty, some S achieves the sup and ↑(S.card) ≤ VCDim
    -- If shatterer is empty, sup = 0 and ↑0 ≤ anything in WithTop ℕ
    simp only [Finset.vcDim, VCDim]
    by_cases h : 𝒜.shatterer.Nonempty
    · -- There exists S ∈ shatterer achieving the sup
      obtain ⟨S, hS, hmax⟩ := Finset.exists_mem_eq_sup _ h Finset.card
      change (↑(𝒜.shatterer.sup Finset.card) : WithTop ℕ) ≤ _
      rw [hmax]
      have hS' : Shatters X (↑C : Set (X → Bool)) S :=
        (shatters_iff_finset_shatters C S).mpr (Finset.mem_shatterer.mp hS)
      exact le_iSup₂_of_le S hS' le_rfl
    · -- shatterer is empty, so sup = 0 = ⊥ ≤ anything
      rw [Finset.not_nonempty_iff_eq_empty] at h
      change (↑(𝒜.shatterer.sup Finset.card) : WithTop ℕ) ≤ _
      simp_all
