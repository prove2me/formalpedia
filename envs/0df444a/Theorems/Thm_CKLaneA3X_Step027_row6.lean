-- Prove2me | Theorems.Thm_CKLaneA3X_Step027_row6
-- name    : CKLaneA3X.Step027.row6
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-25T02:56:42.671169+00:00
-- url     : https://prove2.me/theorems/f8f755b3-ae5d-418d-9351-03be60a0e968
-- title:
--   The complete A3X square output row 6 matches its certificate
-- statement:
--   Output row 6 of the exact square of D_Us.P, truncated to 24 rows, equals the complete stored D_UsUs row. This checks every sparse key and Laurent coefficient in the row.
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

theorem CKLaneA3X.Step027.row6 : (TPoly.mulT D_Us.P D_Us.P 24).getD 6 [] = D_UsUs.P.getD 6 [] := by sorry
