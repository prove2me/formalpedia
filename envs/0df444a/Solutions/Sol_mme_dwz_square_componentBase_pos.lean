-- Prove2me | solution 1 for mme_dwz_square_componentBase_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T07:11:03.562057+00:00
-- url     : https://prove2.me/submissions/8b446048-24dc-438f-bbc5-ec4c834defa9

import Mathlib.Tactic
import Definitions.Def_mme_dwz_square_data

open MME.DWZSquare

set_option autoImplicit false
set_option warningAsError true

theorem solution (tau : ℝ) (s : Fin 15) :
    0 < componentBase tau s := by
  fin_cases s <;>
    simp [componentBase, splitA, splitB] <;>
    positivity
