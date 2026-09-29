-- Prove2me | Theorems.Thm_CKLaneA3X_Step026_entryBounds_D_m
-- name    : CKLaneA3X.Step026.entryBounds_D_m
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-25T00:38:42.926892+00:00
-- url     : https://prove2.me/theorems/7a85c47c-374a-44e3-b738-29e36d8305ce
-- title:
--   Exact rounded A3X input bounds for D_m
-- statement:
--   The complete list of 24 rounded interval bounds for the coefficients of the exact input D_m equals the displayed rational cache. Every entry preserves the original signed Laurent intervals, absolute-value maximum, sigma weight and upward rounding. These are exact equalities, not approximate numerical estimates. They provide one input to the still separate multiplication remainder bound.
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

theorem CKLaneA3X.Step026.entryBounds_D_m : entryBounds D_m.P = [(0 : ℚ), (0 : ℚ), (306381641655 : ℚ) / 549755813888, (0 : ℚ), (4625113140225 : ℚ) / 1099511627776, (0 : ℚ), (2051115671423 : ℚ) / 274877906944, (0 : ℚ), (19033699474239 : ℚ) / 1099511627776, (0 : ℚ), (62507000350669 : ℚ) / 1099511627776, (0 : ℚ), (234993017543595 : ℚ) / 1099511627776, (0 : ℚ), (237413709769809 : ℚ) / 274877906944, (0 : ℚ), (3424265701537063 : ℚ) / 1099511627776, (0 : ℚ), (3674766318159601 : ℚ) / 274877906944, (0 : ℚ), (26362714378386645 : ℚ) / 549755813888, (0 : ℚ), (226933924535320069 : ℚ) / 1099511627776, (0 : ℚ)] := by sorry
