-- Prove2me | Theorems.Thm_CKLaneA3X_Step027_row14
-- name    : CKLaneA3X.Step027.row14
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-25T03:03:40.115992+00:00
-- url     : https://prove2.me/theorems/93f4bad0-7284-457d-87e4-921649b8fe6b
-- title:
--   The complete A3X square output row 14 matches its certificate
-- statement:
--   Output row 14 of the exact square of D_Us.P, truncated to 24 rows, equals the complete stored D_UsUs row. This checks every sparse key and Laurent coefficient in the row.
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

theorem CKLaneA3X.Step027.row14 : (TPoly.mulT D_Us.P D_Us.P 24).getD 14 [] = D_UsUs.P.getD 14 [] := by sorry
