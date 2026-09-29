-- Prove2me | Theorems.Thm_CKLaneA3X_Step026_row5
-- name    : CKLaneA3X.Step026.row5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-25T01:16:07.370754+00:00
-- url     : https://prove2.me/theorems/755d33a3-b9f0-4230-8620-73eea4a960e0
-- title:
--   A3X product row 5 matches its stored certificate
-- statement:
--   The complete exact row 5 of the A3X product truncated to 24 rows equals D_mInner row 5, including all sparse keys and 28 stored Laurent coefficients. Other rows and the analytic validity statement remain separate obligations.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA3X/Step026.lean#L15

import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step026_data

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open CKLaneA3X

theorem CKLaneA3X.Step026.row5 : (TPoly.mulT D_m.P D_inner.P 24).getD 5 [] = D_mInner.P.getD 5 [] := by sorry
