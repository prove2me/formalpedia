-- Prove2me | solution 1 for isCompactSystem_closedCompactCylinders
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T09:35:48.385218+00:00
-- url     : https://prove2.me/submissions/5e2ea220-de43-4900-83ae-a837c056ebfd

import Definitions.Def_KolmogorovExtension4_CompactSystem_F000

/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/

@[expose] public section

open Set MeasureTheory

section definition

variable {α : Type*} {p : Set α → Prop} {C : ℕ → Set α}

end definition

section ClosedCompactCylinders

/-! We prove that the `closedCompactCylinders` are a compact system. -/

variable {ι : Type*} {α : ι → Type*} [∀ i, TopologicalSpace (α i)] {s : ℕ → Set (Π i, α i)}

local notation "Js" => closedCompactCylinders.finset
local notation "As" => closedCompactCylinders.set

section AllProj

end AllProj

section projCylinder

end projCylinder

section piCylinderSet

end piCylinderSet


theorem _root_.solution : IsCompactSystem (closedCompactCylinders α) := by
  intro C hC hC_empty
  by_cases hne : ∀ i, Nonempty (α i)
  · have h : ⋂ n, projCylinder hC n = ∅ := by
      by_contra hc
      obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.mpr hc
      obtain ⟨x, rfl⟩ := surjective_proj_allProj hC y
      have hx : x ∈ ⋂ n, C n := by
        rw [Set.mem_iInter] at hy ⊢
        intro n
        have := hy n
        rw [← preimage_projCylinder hC n]
        exact this
      rw [hC_empty] at hx
      exact hx
    obtain ⟨t, ht⟩ := exists_finset_iInter_projCylinder_eq_empty hC h
    refine ⟨t.sup id, ?_⟩
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    have hx' : (fun i : allProj hC ↦ x (i : ι)) ∈ ⋂ i ∈ t, projCylinder hC i := by
      rw [Set.mem_iInter₂]
      intro i hi
      have hxi : x ∈ C i := by
        simp only [Set.dissipate, Set.mem_iInter] at hx
        exact hx i (Finset.le_sup (f := id) hi)
      rw [← preimage_projCylinder hC i] at hxi
      exact hxi
    rw [ht] at hx'
    exact hx'
  · push_neg at hne
    obtain ⟨i, hi⟩ := hne
    refine ⟨0, ?_⟩
    rw [Set.eq_empty_iff_forall_notMem]
    intro x _
    exact hi.false (x i)

end ClosedCompactCylinders
