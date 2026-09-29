-- Prove2me | Theorems.Thm_CKLaneA3X_Step026_row23_slot4
-- name    : CKLaneA3X.Step026.row23_slot4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-25T00:18:13.026458+00:00
-- url     : https://prove2.me/theorems/4848d388-ad8a-4804-af68-aa02b0cdab3d
-- title:
--   A3X output row 23, slot 4 Laurent block
-- statement:
--   The 13 Laurent entries at sparse-list slot 4 of output row 23 agree between the exact A3X product truncated to 24 rows and the stored D_mInner array. The stored slot has sigma exponent 4; product sparse-key equality is handled by the separate row reconstruction. This block does not assert other slots, other rows, or the remainder bound.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA3X/Step026.lean#L15

import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step026_data

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open CKLaneA3X

theorem CKLaneA3X.Step026.row23_slot4 : (((TPoly.mulT D_m.P D_inner.P 24).getD 23 []).getD 4 (0, [])).2 = ((D_mInner.P.getD 23 []).getD 4 (0, [])).2 := by sorry
