-- Prove2me | Theorems.Thm_CKLaneA3X_Step027_row22_slots16_19
-- name    : CKLaneA3X.Step027.row22_slots16_19
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-25T03:03:12.940365+00:00
-- url     : https://prove2.me/theorems/1658a95d-d2da-4165-a5d4-b5619b1b787f
-- title:
--   A3X square row 22, slots 16–19 Laurent blocks
-- statement:
--   The full Laurent lists at sparse-list positions 16 through 19 in output row 22 of the exact D_Us square match their stored lists. These entries contain 52 Laurent monomials. Actual sparse keys are checked by the separately Proved row reconstruction theorem.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA3X/Step027.lean#L15

import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step027_data_functions

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open CKLaneA3X

theorem CKLaneA3X.Step027.row22_slots16_19 (i : Fin 4) : (((TPoly.mulT D_Us.P D_Us.P 24).getD 22 []).getD (16 + i.val) (0, [])).2 = ((D_UsUs.P.getD 22 []).getD (16 + i.val) (0, [])).2 := by sorry
