-- Prove2me | solution 1 for shatters_iff_finset_shatters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:38:58.91686+00:00
-- url     : https://prove2.me/submissions/e267c7f7-d0db-411c-8848-66c286805ce0

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

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution {X : Type u} [Fintype X] [DecidableEq X]
    (C : Finset (X → Bool)) (S : Finset X) :
    Shatters X (↑C : Set (X → Bool)) S ↔
      (conceptClassToFinsetFamily C).Shatters S := by
  constructor
  · -- (→) Our Shatters → Mathlib Shatters
    intro hShat t ht
    let f : ↥S → Bool := fun x => decide (↑x ∈ t)
    obtain ⟨c, hcC, hcf⟩ := hShat f
    have hcC' : c ∈ C := Finset.mem_coe.mp hcC
    refine ⟨conceptToFinset c, Finset.mem_image.mpr ⟨c, hcC', rfl⟩, ?_⟩
    ext x
    simp only [Finset.mem_inter, conceptToFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hxS, hcx⟩
      have h := hcf ⟨x, hxS⟩
      -- h : c x = decide (x ∈ t), hcx : c x = true
      rw [hcx] at h
      exact decide_eq_true_eq.mp h.symm
    · intro hxt
      refine ⟨ht hxt, ?_⟩
      have h := hcf ⟨x, ht hxt⟩
      -- h : c x = decide (x ∈ t), hxt : x ∈ t
      simp only [f] at h
      rw [h, decide_eq_true_eq]; exact hxt
  · -- (←) Mathlib Shatters → Our Shatters
    intro hShat f
    -- Build t ⊆ S from f: the "true-set" of f within S
    -- Use Subtype.val on S.attach to avoid the membership proof issue
    let t : Finset X := (S.attach.filter (fun x => f x = true)).map
      ⟨Subtype.val, Subtype.val_injective⟩
    have htS : t ⊆ S := by
      intro x hx
      simp only [t, Finset.mem_map, Finset.mem_filter, Finset.mem_attach, true_and,
        Function.Embedding.coeFn_mk] at hx
      obtain ⟨⟨y, hyS⟩, _, rfl⟩ := hx
      exact hyS
    obtain ⟨u, huA, hSu⟩ := hShat htS
    simp only [conceptClassToFinsetFamily, Finset.mem_image] at huA
    obtain ⟨c, hcC, rfl⟩ := huA
    refine ⟨c, Finset.mem_coe.mpr hcC, ?_⟩
    intro ⟨x, hxS⟩
    -- From hSu: S ∩ conceptToFinset c = t
    -- x ∈ S, so: c x = true ↔ x ∈ t ↔ f ⟨x, hxS⟩ = true
    have hx_in_inter : x ∈ S ∩ conceptToFinset c ↔ x ∈ t :=
      Finset.ext_iff.mp hSu x
    have hx_in_t : x ∈ t ↔ f ⟨x, hxS⟩ = true := by
      simp only [t, Finset.mem_map, Finset.mem_filter, Finset.mem_attach, true_and,
        Function.Embedding.coeFn_mk]
      simp_all
    have hx_cx : x ∈ S ∩ conceptToFinset c ↔ c x = true := by
      simp only [Finset.mem_inter, conceptToFinset, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact ⟨fun h => h.2, fun h => ⟨hxS, h⟩⟩
    -- Combine: c x = true ↔ f ⟨x, hxS⟩ = true
    simp_all
