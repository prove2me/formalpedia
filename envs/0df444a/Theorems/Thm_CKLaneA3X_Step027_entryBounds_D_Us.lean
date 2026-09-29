-- Prove2me | Theorems.Thm_CKLaneA3X_Step027_entryBounds_D_Us
-- name    : CKLaneA3X.Step027.entryBounds_D_Us
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-25T03:00:06.839402+00:00
-- url     : https://prove2.me/theorems/35418256-d858-41f5-85c8-1a03ca18058b
-- title:
--   Exact rounded A3X square input bounds
-- statement:
--   The complete list of 24 rounded interval bounds for D_Us.P equals the displayed rational cache. Each entry uses the original signed Laurent intervals, absolute-value maximum, sigma weight and upward rounding. The same input occurs twice in Step027, so this one exact list serves both sides of the square remainder formula.
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

theorem CKLaneA3X.Step027.entryBounds_D_Us : entryBounds D_Us.P = [(0 : ℚ), (306381641655 : ℚ) / 549755813888, (0 : ℚ), (1499479667313 : ℚ) / 549755813888, (0 : ℚ), (2322557212633 : ℚ) / 1099511627776, (0 : ℚ), (3959951669649 : ℚ) / 549755813888, (0 : ℚ), (35073693232377 : ℚ) / 1099511627776, (0 : ℚ), (38934953257953 : ℚ) / 274877906944, (0 : ℚ), (586731665530877 : ℚ) / 1099511627776, (0 : ℚ), (8886011926605 : ℚ) / 4294967296, (0 : ℚ), (4149713315115945 : ℚ) / 549755813888, (0 : ℚ), (30998574873131219 : ℚ) / 1099511627776, (0 : ℚ), (14540618314931331 : ℚ) / 137438953472, (0 : ℚ), (338887962548126507 : ℚ) / 1099511627776] := by sorry
