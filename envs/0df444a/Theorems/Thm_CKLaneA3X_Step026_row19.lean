-- Prove2me | Theorems.Thm_CKLaneA3X_Step026_row19
-- name    : CKLaneA3X.Step026.row19
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-25T01:28:44.42891+00:00
-- url     : https://prove2.me/theorems/a7cbac37-2003-48a1-a8ea-cb600f88eabb
-- title:
--   The complete A3X product row 19 matches its certificate
-- statement:
--   The complete sparse product row 19 equals the stored D_mInner row, including every sparse key and all Laurent lists. It combines 11 proved two-slot block theorems with the proved sparse-key reconstruction. Other polynomial rows and the analytic validity statement remain separate.
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

theorem CKLaneA3X.Step026.row19 : (TPoly.mulT D_m.P D_inner.P 24).getD 19 [] = D_mInner.P.getD 19 [] := by sorry
