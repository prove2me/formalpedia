-- Prove2me | Theorems.Thm_CKLaneA3X_Step026_row23_slot23
-- name    : CKLaneA3X.Step026.row23_slot23
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-25T00:26:23.584948+00:00
-- url     : https://prove2.me/theorems/9b2c18ee-7c00-4ec3-974e-d2151a50b4ad
-- title:
--   A3X output row 23, slot 23 Laurent block
-- statement:
--   The 13 Laurent entries at sparse-list slot 23 of output row 23 agree between the exact A3X product truncated to 24 rows and the stored D_mInner array. The stored slot has sigma exponent 23; product sparse-key equality is handled by the separate row reconstruction. This block does not assert other slots, other rows, or the remainder bound.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA3X/Step026.lean#L15

import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step026_data

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open CKLaneA3X

theorem CKLaneA3X.Step026.row23_slot23 : (((TPoly.mulT D_m.P D_inner.P 24).getD 23 []).getD 23 (0, [])).2 = ((D_mInner.P.getD 23 []).getD 23 (0, [])).2 := by sorry
