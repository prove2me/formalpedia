-- Prove2me | Theorems.Thm_CKLaneA3X_Step026_row9
-- name    : CKLaneA3X.Step026.row9
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-25T01:16:14.003531+00:00
-- url     : https://prove2.me/theorems/87c475f3-aaf4-4544-9edb-2efff0f03f17
-- title:
--   A3X product row 9 matches its stored certificate
-- statement:
--   The complete exact row 9 of the A3X product truncated to 24 rows equals D_mInner row 9, including all sparse keys and 71 stored Laurent coefficients. Other rows and the analytic validity statement remain separate obligations.
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

theorem CKLaneA3X.Step026.row9 : (TPoly.mulT D_m.P D_inner.P 24).getD 9 [] = D_mInner.P.getD 9 [] := by sorry
