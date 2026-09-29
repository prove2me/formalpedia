-- Prove2me | Theorems.Thm_CKLaneA3X_Step027_remainder_bound
-- name    : CKLaneA3X.Step027.remainder_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-25T03:06:51.355376+00:00
-- url     : https://prove2.me/theorems/97404d68-2f18-4f2a-a12f-10dde7ad73bb
-- title:
--   The A3X square remainder fits its stored bound
-- statement:
--   The rounded remainder of the exact truncated square of D_Us, with both vanishing-prefix parameters equal to 1 and truncation 24, is at most the stored D_UsUs remainder. This is the exact compact form of Step027’s final numerical premise. One proved rounded input-bound list serves both occurrences of the same input; the original remainder formula and rounding rule are unchanged.
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

theorem CKLaneA3X.Step027.remainder_bound : (TMd.mul D_Us D_Us 1 1 24).r ≤ D_UsUs.r := by sorry
