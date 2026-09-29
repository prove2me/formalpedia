-- Prove2me | solution 1 for mme_dwz_table2_canonical_address_block_component_power_iso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T06:45:07.253576+00:00
-- url     : https://prove2.me/submissions/ce29e9a9-c382-4fa0-98e8-630d7f7d8a13

import Definitions.Def_mme_dwz_table2_integer_counts
import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_mme_CW_square_canonical_grading
import Definitions.Def_mme_CW_square_five_grade_certificate
import Theorems.Thm_mme_kronFin_group_by_exact_fibers_iso

open MME
open MME.DWZSquare

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] {N m : ℕ}
    (word : Fin N → Fin 15)
    (hword : ∀ s : Fin 15,
      Fintype.card {r : Fin N // word r = s} =
        MME.DWZTable2Counts.component s * m) :
    let G := cwSquareCanonicalGrading K 6
    let componentBlock : Fin 15 → TensorObj K 3 := fun s ↦
      G.blockSubtensor
        (cwSquareBlockType (shapeX s) (shapeY s) (shapeZ s))
    let address : Fin 3 → Fin N → Fin 5 := fun i r ↦
      cwSquareBlockType
        (shapeX (word r)) (shapeY (word r)) (shapeZ (word r)) i
    TensorObj.Isomorphic
      (gradedAddressBlock G address)
      (TensorObj.kronFin 15 (fun s ↦
        (componentBlock s).kronPow
          (MME.DWZTable2Counts.component s * m))) := by
  dsimp only
  change TensorObj.Isomorphic
    (TensorObj.kronFin N (fun r ↦
      (cwSquareCanonicalGrading K 6).blockSubtensor
        (cwSquareBlockType
          (shapeX (word r)) (shapeY (word r)) (shapeZ (word r)))))
    (TensorObj.kronFin 15 (fun s ↦
      ((cwSquareCanonicalGrading K 6).blockSubtensor
        (cwSquareBlockType (shapeX s) (shapeY s) (shapeZ s))).kronPow
          (MME.DWZTable2Counts.component s * m)))
  exact mme_kronFin_group_by_exact_fibers_iso
    (fun s : Fin 15 ↦
      (cwSquareCanonicalGrading K 6).blockSubtensor
        (cwSquareBlockType (shapeX s) (shapeY s) (shapeZ s)))
    word (fun s ↦ MME.DWZTable2Counts.component s * m) hword
