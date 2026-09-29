-- Prove2me | Theorems.Thm_CKLaneA3X_Step027_empty_rows
-- name    : CKLaneA3X.Step027.empty_rows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-25T02:46:09.968915+00:00
-- url     : https://prove2.me/theorems/beb59454-2711-4662-92ad-01823ebf11a0
-- title:
--   All 13 empty A3X square output rows match their certificates
-- statement:
--   For the explicit row indices 0, 1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, the actual truncated square row equals the stored empty row. Each actual row is kernel-checked; its emptiness is not inferred only from the certificate.
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

theorem CKLaneA3X.Step027.empty_rows (i : Fin 13) : (TPoly.mulT D_Us.P D_Us.P 24).getD (([0, 1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23] : List Nat).getD i 0) [] = D_UsUs.P.getD (([0, 1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23] : List Nat).getD i 0) [] := by sorry
