-- Prove2me | Theorems.Thm_CKLaneA3X_Step026_row23_slot8
-- name    : CKLaneA3X.Step026.row23_slot8
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-25T00:01:36.628352+00:00
-- url     : https://prove2.me/theorems/471f948a-42fe-4808-83a3-a3ae4d42dc14
-- title:
--   A3X output row 23, slot 8 Laurent block
-- statement:
--   In the exact rational A3X multiplication arrays, the 13 Laurent entries at output row 23, sparse-list slot 8, agree between the product truncated to 24 rows and the stored result D_mInner. The stored slot has sigma exponent 8; product key/shape equality is a separate reconstruction check. This is one newly generated certificate block, not the full Step026 polynomial identity or remainder bound.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA3X/Step026.lean#L15

import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step026_data

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open CKLaneA3X

theorem CKLaneA3X.Step026.row23_slot8  : (((TPoly.mulT D_m.P D_inner.P 24).getD 23 []).getD 8 (0, [])).2 = ((D_mInner.P.getD 23 []).getD 8 (0, [])).2 := by sorry
