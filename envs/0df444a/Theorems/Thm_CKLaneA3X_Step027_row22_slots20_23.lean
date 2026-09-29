-- Prove2me | Theorems.Thm_CKLaneA3X_Step027_row22_slots20_23
-- name    : CKLaneA3X.Step027.row22_slots20_23
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-25T02:46:17.369847+00:00
-- url     : https://prove2.me/theorems/eb852bcf-dbf9-4583-a901-783535c16d26
-- title:
--   A3X square row 22, slots 20–23 Laurent blocks
-- statement:
--   The four full Laurent lists at sparse-list positions 20 through 23 in the largest nonempty square output row match their stored lists. The stored entries contain 52 Laurent monomials and have sigma exponents 20 through 23. Equality of the actual sparse keys is a separate reconstruction obligation.
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

theorem CKLaneA3X.Step027.row22_slots20_23 (i : Fin 4) : (((TPoly.mulT D_Us.P D_Us.P 24).getD 22 []).getD (20 + i.val) (0, [])).2 = ((D_UsUs.P.getD 22 []).getD (20 + i.val) (0, [])).2 := by sorry
