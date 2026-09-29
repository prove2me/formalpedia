-- Prove2me | solution 1 for mme_dwz_table2_completed_fine_words_boundary_histograms
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T10:18:53.993136+00:00
-- url     : https://prove2.me/submissions/c2f544a6-9f22-48d8-a07f-a4a4d2d12984

import Definitions.Def_mme_dwz_table2_completed_fine_words
import Definitions.Def_mme_dwz_table2_useful_block

open MME
open MME.DWZStep2Source

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (m : ℕ) {Position : Type u} [Fintype Position]
    (outer : Position → Fin 15)
    (small : MME.DWZTable2StandardForm.UsefulBlock m outer) :
    (∀ (s : Fin 15), MME.DWZSquare.shapeY s = 0 →
      ∀ a : Fin 3,
        Fintype.card {t : Position //
          outer t = s ∧
          (completedFineLeft outer small.1 small.2.1 0 t).val + a.val = 2} =
          MME.DWZTable2Counts.split s a * m) ∧
    (∀ (s : Fin 15), MME.DWZSquare.shapeX s = 0 →
      ∀ a : Fin 3,
        Fintype.card {t : Position //
          outer t = s ∧
          (completedFineLeft outer small.1 small.2.1 1 t).val + a.val = 2} =
          MME.DWZTable2Counts.split s a * m) := by
  constructor
  · intro s hs a
    have hiff (t : Position) (ht : outer t = s) :
        (completedFineLeft outer small.1 small.2.1 0 t).val + a.val = 2 ↔
          (small.1 t).1 = a := by
      let c := fineXYCompletion (outer t) (small.1 t).1 (small.1 t).2 (small.2.1 t)
      have hs0 : (MME.DWZSquare.shapeY (outer t)).val = 0 := by
        simpa [ht] using congrArg Fin.val hs
      have hy : c.yLeft.val + c.yRight.val = 0 := c.y_coarse.trans hs0
      have hy0 : c.yLeft.val = 0 := by omega
      have hsupp := c.left_support
      have hxz : c.xLeft.val + (small.1 t).1.val = 2 := by omega
      change c.xLeft.val + a.val = 2 ↔ (small.1 t).1 = a
      constructor
      · intro hxa
        apply Fin.ext
        omega
      · intro hza
        rw [← hza]
        exact hxz
    let e :
        {t : Position //
          outer t = s ∧
          (completedFineLeft outer small.1 small.2.1 0 t).val + a.val = 2} ≃
        {t : Position // outer t = s ∧ (small.1 t).1 = a} :=
      { toFun := fun t ↦ ⟨t.1, t.2.1, (hiff t.1 t.2.1).mp t.2.2⟩
        invFun := fun t ↦ ⟨t.1, t.2.1, (hiff t.1 t.2.1).mpr t.2.2⟩
        left_inv := by intro t; apply Subtype.ext; rfl
        right_inv := by intro t; apply Subtype.ext; rfl }
    exact (Fintype.card_congr e).trans (small.2.2 s a)
  · intro s hs a
    have hiff (t : Position) (ht : outer t = s) :
        (completedFineLeft outer small.1 small.2.1 1 t).val + a.val = 2 ↔
          (small.1 t).1 = a := by
      let c := fineXYCompletion (outer t) (small.1 t).1 (small.1 t).2 (small.2.1 t)
      have hs0 : (MME.DWZSquare.shapeX (outer t)).val = 0 := by
        simpa [ht] using congrArg Fin.val hs
      have hx : c.xLeft.val + c.xRight.val = 0 := c.x_coarse.trans hs0
      have hx0 : c.xLeft.val = 0 := by omega
      have hsupp := c.left_support
      have hyz : c.yLeft.val + (small.1 t).1.val = 2 := by omega
      change c.yLeft.val + a.val = 2 ↔ (small.1 t).1 = a
      constructor
      · intro hya
        apply Fin.ext
        omega
      · intro hza
        rw [← hza]
        exact hyz
    let e :
        {t : Position //
          outer t = s ∧
          (completedFineLeft outer small.1 small.2.1 1 t).val + a.val = 2} ≃
        {t : Position // outer t = s ∧ (small.1 t).1 = a} :=
      { toFun := fun t ↦ ⟨t.1, t.2.1, (hiff t.1 t.2.1).mp t.2.2⟩
        invFun := fun t ↦ ⟨t.1, t.2.1, (hiff t.1 t.2.1).mpr t.2.2⟩
        left_inv := by intro t; apply Subtype.ext; rfl
        right_inv := by intro t; apply Subtype.ext; rfl }
    exact (Fintype.card_congr e).trans (small.2.2 s a)
