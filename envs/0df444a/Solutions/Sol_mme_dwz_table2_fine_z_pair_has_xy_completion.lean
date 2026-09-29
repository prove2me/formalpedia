-- Prove2me | solution 1 for mme_dwz_table2_fine_z_pair_has_xy_completion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T09:44:42.775316+00:00
-- url     : https://prove2.me/submissions/727c2783-1bbe-45f7-aee7-3872f7e234a1

import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_dwz_table2_pair_coarsening

open MME

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (s : Fin 15) (zLeft zRight : Fin 3)
    (hZ : MME.DWZTable2Counts.coarseOf (zLeft, zRight) =
      MME.DWZSquare.shapeZ s) :
    ∃ xLeft xRight yLeft yRight : Fin 3,
      xLeft.val + xRight.val = (MME.DWZSquare.shapeX s).val ∧
      yLeft.val + yRight.val = (MME.DWZSquare.shapeY s).val ∧
      xLeft.val + yLeft.val + zLeft.val = 2 ∧
      xRight.val + yRight.val + zRight.val = 2 := by
  fin_cases s <;> fin_cases zLeft <;> fin_cases zRight <;>
    simp [MME.DWZTable2Counts.coarseOf, MME.DWZSquare.shapeZ] at hZ <;>
    first | contradiction | decide
