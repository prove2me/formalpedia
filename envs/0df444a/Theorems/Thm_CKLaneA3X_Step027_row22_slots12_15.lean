-- Prove2me | Theorems.Thm_CKLaneA3X_Step027_row22_slots12_15
-- name    : CKLaneA3X.Step027.row22_slots12_15
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-25T03:03:05.658321+00:00
-- url     : https://prove2.me/theorems/b6e6b96d-1d98-4851-8202-41c5ef89c185
-- title:
--   A3X square row 22, slots 12–15 Laurent blocks
-- statement:
--   The full Laurent lists at sparse-list positions 12 through 15 in output row 22 of the exact D_Us square match their stored lists. These entries contain 52 Laurent monomials. Actual sparse keys are checked by the separately Proved row reconstruction theorem.
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

theorem CKLaneA3X.Step027.row22_slots12_15 (i : Fin 4) : (((TPoly.mulT D_Us.P D_Us.P 24).getD 22 []).getD (12 + i.val) (0, [])).2 = ((D_UsUs.P.getD 22 []).getD (12 + i.val) (0, [])).2 := by sorry
