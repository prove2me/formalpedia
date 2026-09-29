-- Prove2me | Theorems.Thm_CKLaneA3X_Step026_row23
-- name    : CKLaneA3X.Step026.row23
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-25T00:33:16.434648+00:00
-- url     : https://prove2.me/theorems/ee79ee06-5fde-417e-82c8-c7690b8f5251
-- title:
--   The full A3X product row23 matches its certificate
-- statement:
--   Row 23 of the exact A3X product truncated to 24 rows equals row 23 of D_mInner. This new certificate fragment assembles all 26 proved Laurent-list blocks with the proved sparse-key reconstruction. It does not assert the other output rows, the full polynomial equality, or the remainder bound.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA3X/Step026.lean#L15

import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step026_data

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open CKLaneA3X

theorem CKLaneA3X.Step026.row23 : (TPoly.mulT D_m.P D_inner.P 24).getD 23 [] = D_mInner.P.getD 23 [] := by sorry
