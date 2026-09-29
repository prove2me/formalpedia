-- Prove2me | solution 1 for mme_dwz_table2_useful_z_and_fine_support_implies_step1_xy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T21:02:38.930668+00:00
-- url     : https://prove2.me/submissions/e03857e8-4b6a-4f2d-9dd1-c129433e6acf

import Theorems.Thm_mme_CW_square_fine_split_support
import Definitions.Def_mme_dwz_table2_integer_counts
import Definitions.Def_mme_dwz_square_data

open MME MME.DWZStep1Support

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] (q m : ℕ)
    {Position : Type*} [Fintype Position]
    (outer : Position → Fin 15)
    (left right : Fin 3 → Position → Fin 3)
    (hCoarse : ∀ i t,
      (left i t).val + (right i t).val =
        (![MME.DWZSquare.shapeX (outer t),
          MME.DWZSquare.shapeY (outer t),
          MME.DWZSquare.shapeZ (outer t)] i).val)
    (hFineSupport : ∀ t,
      (cwSquareFineSplitGrading K q).blockTensor
        (fun i ↦ fineSplitGrade (left i t) (right i t)) ≠ 0)
    (hZUseful : ∀ (s : Fin 15) (a : Fin 3),
      Fintype.card {t : Position // outer t = s ∧ left 2 t = a} =
        MME.DWZTable2Counts.split s a * m) :
    (∀ (s : Fin 15), MME.DWZSquare.shapeY s = 0 →
      ∀ a : Fin 3,
        Fintype.card {t : Position //
          outer t = s ∧ (left 0 t).val + a.val = 2} =
          MME.DWZTable2Counts.split s a * m) ∧
    (∀ (s : Fin 15), MME.DWZSquare.shapeX s = 0 →
      ∀ a : Fin 3,
        Fintype.card {t : Position //
          outer t = s ∧ (left 1 t).val + a.val = 2} =
          MME.DWZTable2Counts.split s a * m) := by
  classical
  have hLeftSupport : ∀ t,
      (left 0 t).val + (left 1 t).val + (left 2 t).val = 2 := by
    intro t
    exact (mme_CW_square_fine_split_support K q
      (fun i ↦ left i t) (fun i ↦ right i t) (hFineSupport t)).1
  constructor
  · intro s hsY a
    let e :
        {t : Position //
          outer t = s ∧ (left 0 t).val + a.val = 2} ≃
        {t : Position // outer t = s ∧ left 2 t = a} :=
      { toFun := fun t ↦ ⟨t.1, t.2.1, by
          apply Fin.ext
          have hy := hCoarse 1 t.1
          rw [t.2.1] at hy
          have hs := hLeftSupport t.1
          have hxa : (left 0 t.1).val + a.val = 2 := t.2.2
          simp [hsY] at hy
          omega⟩
        invFun := fun t ↦ ⟨t.1, t.2.1, by
          have hy := hCoarse 1 t.1
          rw [t.2.1] at hy
          have hs := hLeftSupport t.1
          have hz := congrArg Fin.val t.2.2
          simp [hsY] at hy
          omega⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    rw [Fintype.card_congr e]
    exact hZUseful s a
  · intro s hsX a
    let e :
        {t : Position //
          outer t = s ∧ (left 1 t).val + a.val = 2} ≃
        {t : Position // outer t = s ∧ left 2 t = a} :=
      { toFun := fun t ↦ ⟨t.1, t.2.1, by
          apply Fin.ext
          have hx := hCoarse 0 t.1
          rw [t.2.1] at hx
          have hs := hLeftSupport t.1
          have hya : (left 1 t.1).val + a.val = 2 := t.2.2
          simp [hsX] at hx
          omega⟩
        invFun := fun t ↦ ⟨t.1, t.2.1, by
          have hx := hCoarse 0 t.1
          rw [t.2.1] at hx
          have hs := hLeftSupport t.1
          have hz := congrArg Fin.val t.2.2
          simp [hsX] at hx
          omega⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    rw [Fintype.card_congr e]
    exact hZUseful s a
