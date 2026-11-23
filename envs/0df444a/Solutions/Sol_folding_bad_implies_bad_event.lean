-- Prove2me | solution 1 for folding_bad_implies_bad_event
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:29:01.924524+00:00
-- url     : https://prove2.me/submissions/06c24aea-65aa-43fd-8318-6437f328b95b

import Definitions.Def_SimpleRbrFri_State
import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Theorems.Thm_fold_eq_sum_components
import Theorems.Thm_reconstruct_func_in_code
import Theorems.Thm_reconstruction_from_components


set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution [Fintype F]
  (D : Finset F) (m : ℕ) (d : ℕ) (hm : m > 0) (f : D → F) (alpha : F) (delta : ℝ)
  (h_bad : Folding_Bad_Event D m d f alpha delta) :
  BadEvent (reedSolomon (pow_domain D m) (d / m)) m
      (folding_components D m (extend_by_zero D f)) delta (fun i ↦ alpha ^ (i : ℕ)) := by
  contrapose! h_bad with h
  intro h_bad_event
  obtain ⟨S, hS₁, hS₂, hS₃, hS₄⟩ := h_bad_event
  refine h ⟨?_, ?_, ?_, ?_⟩
  · exact Finset.filter (fun x ↦ x.val ∈ pow_domain S m)
      (Finset.univ : Finset ({x : F // x ∈ pow_domain D m}))
  · rw [Fintype.card_coe]
    convert hS₂ using 2
    refine Finset.card_bij (fun x _ ↦ x.val) ?_ ?_ ?_
    · intro x hx; exact (Finset.mem_filter.mp hx).2
    · intro x₁ _ x₂ _ h; exact Subtype.ext h
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact ⟨⟨x ^ m, Finset.mem_image.mpr ⟨x, hS₁ hx, rfl⟩⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩, rfl⟩
  · obtain ⟨u, hu₁, hu₂⟩ := hS₃
    refine ⟨u, hu₁, fun x hx ↦ ?_⟩
    convert (hu₂ x (Finset.mem_filter.mp hx).2).symm using 1
    · unfold extend_by_zero; grind
    · exact (fold_eq_sum_components D m hm (extend_by_zero D f) alpha ↑x).symm
  · by_contra! h_contra
    choose u hu using h_contra
    have h_reconstruct : (D : Set F).restrict (reconstruct_func m
        (fun i z ↦ if h : z ∈ pow_domain D m then u i ⟨z, h⟩ else 0))
        ∈ reedSolomon D d := by
      apply_rules [reconstruct_func_in_code]
      intro i
      have h_eq : (↑(pow_domain D m) : Set F).restrict (fun z ↦ if h : z ∈ pow_domain D m then u i ⟨z, h⟩ else 0) = u i := by
        ext z; exact dif_pos z.2
      rw [h_eq]; exact (hu i).1
    refine hS₄ _ h_reconstruct ?_
    intro x hx
    have hxD : x ∈ D := hS₁ hx
    have hxm : x ^ m ∈ pow_domain D m := Finset.mem_image_of_mem _ hxD
    rw [extend_by_zero, extend_by_zero, dif_pos hxD, dif_pos hxD]
    change f ⟨x, hxD⟩ = reconstruct_func m (fun i z ↦ if h : z ∈ pow_domain D m then u i ⟨z, h⟩ else 0) x
    rw [reconstruct_func]
    have hrec := reconstruction_from_components D m hm (extend_by_zero D f) x hxD
    rw [extend_by_zero, dif_pos hxD] at hrec
    rw [hrec]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [dif_pos hxm]
    have hmem : (⟨x ^ m, hxm⟩ : pow_domain D m) ∈ Finset.filter (fun z : pow_domain D m ↦ z.val ∈ pow_domain S m) Finset.univ :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_image_of_mem _ hx⟩
    exact congrArg (· * x ^ (i : ℕ)) ((hu i).2 ⟨x ^ m, hxm⟩ hmem).symm
