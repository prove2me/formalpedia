-- Prove2me | solution 1 for mme_dwz_table2_completed_fine_words_total_z_histogram
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T10:29:24.311661+00:00
-- url     : https://prove2.me/submissions/93e4a359-5dca-42bc-9cef-0c52350bfa61

import Definitions.Def_mme_dwz_table2_completed_fine_words
import Definitions.Def_mme_dwz_table2_useful_block
import Definitions.Def_mme_dwz_table2_step1_z_histogram_fibers
import Theorems.Thm_mme_dwz_table2_split_sum_at_z_degree

open MME BigOperators
open MME.DWZStep1Histogram
open MME.DWZStep2Source

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (m : ℕ) {Position : Type u} [Fintype Position]
    (outer : Position → Fin 15)
    (small : MME.DWZTable2StandardForm.UsefulBlock m outer) :
    ∀ (k : Fin 5) (a : Fin 3),
      Fintype.card
          (TotalZFiber outer
            (completedFineLeft outer small.1 small.2.1 2) k a) =
        table2TotalZSplit k a * m := by
  intro k a
  let e :
      (Σ s : {s : Fin 15 // MME.DWZSquare.shapeZ s = k},
        {t : Position // outer t = s.1 ∧ (small.1 t).1 = a}) ≃
        TotalZFiber outer (fun t ↦ (small.1 t).1) k a :=
    { toFun := fun x ↦ ⟨x.2.1,
        ⟨by rw [x.2.2.1]; exact x.1.2, x.2.2.2⟩⟩
      invFun := fun t ↦ ⟨⟨outer t.1, t.2.1⟩, ⟨t.1, rfl, t.2.2⟩⟩
      left_inv := by
        intro x
        rcases x with ⟨⟨s, hs⟩, ⟨t, ht, ha⟩⟩
        cases ht
        rfl
      right_inv := by intro t; cases t; rfl }
  change Fintype.card
      (TotalZFiber outer (fun t ↦ (small.1 t).1) k a) = _
  rw [← Fintype.card_congr e, Fintype.card_sigma]
  simp_rw [small.2.2]
  rw [← Finset.sum_mul, mme_dwz_table2_split_sum_at_z_degree]
