-- Prove2me | solution 1 for folding_event_implies_bad_event
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:30:57.473722+00:00
-- url     : https://prove2.me/submissions/a351a60b-7fd9-4264-8b1b-ea71ab4840c3

import Definitions.Def_SimpleRbrFri_State
import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Theorems.Thm_fold_eq_sum_components
import Theorems.Thm_folding_components_in_code_implies_f_in_code


set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution
    (D : Finset F) (m : ℕ) (d : ℕ) (hm : m > 0) (hd : d ≥ m)
    (f : F → F) (delta : ℝ) (r : F)
    (h_event : FoldingBadEvent D m (reedSolomon D d)
      (reedSolomon (pow_domain D m) (d / m)) f delta r) :
    BadEvent (reedSolomon (pow_domain D m) (d / m)) m (folding_components D m f) delta
      (fun i ↦ r ^ (i : ℕ)) := by
  obtain ⟨S, hS, h⟩ := h_event
  refine ⟨Finset.univ.filter fun x ↦ x.val ∈ pow_domain S m, ?_, ?_, ?_⟩
  · simp only [Finset.univ_eq_attach, Fintype.card_coe, ge_iff_le]
    convert h.1.le
    refine Finset.card_bij (fun x _ ↦ x) ?_ ?_ ?_ <;>
      simp only [Finset.mem_filter, Finset.mem_attach, true_and, Subtype.forall,
        Subtype.mk.injEq, imp_self, implies_true, exists_prop, Subtype.exists,
        exists_eq_right_right]
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
    exact ⟨Finset.mem_image.mpr ⟨y, hS hy, rfl⟩, hx⟩
  · obtain ⟨u', hu', hu''⟩ := h.2.1
    refine ⟨u', hu', fun x hx ↦ ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    have h_eq := hu'' x.val hx
    simp only [dif_pos x.2] at h_eq
    exact h_eq.symm ▸ fold_eq_sum_components D m hm f r x.val
  · contrapose! h
    choose u hu using h
    have := folding_components_in_code_implies_f_in_code D m d hm f S hS u
      (fun i ↦ hu i |>.1) (fun i z hz ↦ ?_)
    · grind
    · split_ifs <;> simp_all only [gt_iff_lt, ge_iff_le, pow_domain, Finset.mem_image,
        Finset.univ_eq_attach, Finset.mem_filter, Finset.mem_attach, true_and, forall_exists_index,
        and_imp, Subtype.forall, forall_and_index, not_exists, not_and]
      · obtain ⟨a, ha, rfl⟩ := hz
        exact (hu i |>.2 _ _ (hS ha) rfl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, a, ha, rfl⟩)).symm
      · exact absurd hz.choose_spec.2 (‹∀ x ∈ D, ¬x ^ m = z› _ (hS hz.choose_spec.1))
