-- Prove2me | Theorems.Thm_CKLaneA3X_Step026_remainder_bound
-- name    : CKLaneA3X.Step026.remainder_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-25T00:46:14.608985+00:00
-- url     : https://prove2.me/theorems/66d88a5f-9809-48a0-a9e0-3ecc434b9988
-- title:
--   The A3X multiplication remainder fits its stored bound
-- statement:
--   The rounded remainder of the exact truncated multiplication of D_m and D_inner, with vanishing-prefix parameters2 and1 and truncation24, is at most the stored D_mInner remainder. This is the exact compact form of the final numerical premise in Step026. It uses the two proved rounded coefficient-bound lists and preserves the original remainder formula and rounding rule. Polynomial equality and the other validity premises remain separate.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA3X/Step026.lean#L15

import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step026_data

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open CKLaneA3X

theorem CKLaneA3X.Step026.remainder_bound : (TMd.mul D_m D_inner 2 1 24).r ≤ D_mInner.r := by sorry
