-- Prove2me | solution 1 for mme_dwz_completed_fine_z_address_eq_useful_block_encode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T12:12:23.95015+00:00
-- url     : https://prove2.me/submissions/ff436b68-9876-4813-a523-918518d4e3a8

import Definitions.Def_mme_dwz_table2_completed_fine_words
import Definitions.Def_mme_dwz_table2_useful_block
import Definitions.Def_mme_dwz_retained_fine_address

open MME
open MME.DWZStep1Support
open MME.DWZStep2Source

universe u v

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (m : ℕ) {Copy : Type v} {Position : Type u} [Fintype Position]
    (outer : Copy → Position → Fin 15)
    (small : ∀ j : Copy,
      MME.DWZTable2StandardForm.UsefulBlock m (outer j))
    (j : Copy) :
    let left : Copy → Fin 3 → Position → Fin 3 := fun j' ↦
      completedFineLeft (outer j') (small j').1 (small j').2.1
    let right : Copy → Fin 3 → Position → Fin 3 := fun j' ↦
      completedFineRight (outer j') (small j').1 (small j').2.1
    retainedFineAddress left right j 2 =
      fun t ↦ fineSplitGrade ((small j).1 t).1 ((small j).1 t).2 := by
  dsimp only
  funext t
  simp [retainedFineAddress, completedFineLeft, completedFineRight]
