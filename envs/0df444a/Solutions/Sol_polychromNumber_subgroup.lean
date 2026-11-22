-- Prove2me | solution 1 for polychromNumber_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:43:43.671385+00:00
-- url     : https://prove2.me/submissions/7b64e6c2-2b6d-4486-85ca-687039b85871

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
import Theorems.Thm_le_polychromNumber
import Theorems.Thm_polychromNumber_singleton
import Theorems.Thm_polychromNumber_univ
import Theorems.Thm_polychromNumber_image
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
attribute [local simp] hasPolychromColouring_neg
attribute [local simp] hasPolychromColouring_univ


attribute [local simp] polychromNumber_singleton
attribute [local simp] polychromNumber_univ

set_option autoImplicit true
variable {G : Type*} [AddCommGroup G] {S : Finset G} {K : Type*}
open Finset Fintype Pointwise
theorem _root_.solution [DecidableEq G] (H : AddSubgroup G) {S : Finset H} :
    polychromNumber S = polychromNumber (G := G) (S.image H.subtype) := by
  obtain rfl | hS' := S.eq_empty_or_nonempty
  · simp
  apply le_antisymm _ (polychromNumber_image H.subtype)
  obtain ⟨χ', hχ'⟩ := hasPolychromColouring_fin hS'
  let v (g : G) : G := Quotient.out (QuotientAddGroup.mk g : G ⧸ H) - Quotient.out (0 : G ⧸ H)
  have hv (g : G) : g - v g ∈ H := by
    obtain ⟨a, ha⟩ := QuotientAddGroup.mk_out_eq_mul H g
    obtain ⟨b, hb⟩ := QuotientAddGroup.mk_out_eq_mul H 0
    simp only [QuotientAddGroup.mk_zero, zero_add] at hb
    have : g - (g + a - b) = (b - a : H) := by simp; abel
    simp only [v, ha, hb, this]
    exact SetLike.coe_mem (b - a)
  let h (g : G) : H := ⟨g - v g, hv g⟩
  have h_idem (i : H) : h i = i := by
    ext1
    simp only [sub_eq_self, v, h, sub_eq_zero, Quotient.out_inj, ← QuotientAddGroup.mk_zero]
    rw [QuotientAddGroup.eq_iff_sub_mem]
    simp
  have h_v (i : H) (g : G) : h (i + v g) = i := by
    have : v (i + v g) = v g := by
      rw [sub_left_inj, Quotient.out_inj, eq_comm, QuotientAddGroup.eq_iff_sub_mem,
        sub_add_eq_sub_sub_swap]
      exact H.sub_mem (hv _) (SetLike.coe_mem i)
    simp [h, this]
  let χ : G → Fin (polychromNumber S) := fun g ↦ χ' (h g)
  suffices IsPolychrom (S.image H.subtype) χ from le_polychromNumber ⟨χ, this⟩
  intro g k
  obtain ⟨i, hi, hi'⟩ := hχ' (h g) k
  refine ⟨i, by simpa, ?_⟩
  have : g = h g + v g := by simp [h]
  simp only [χ]
  rw [this, add_right_comm, ← AddSubgroup.coe_add, h_v, hi']
