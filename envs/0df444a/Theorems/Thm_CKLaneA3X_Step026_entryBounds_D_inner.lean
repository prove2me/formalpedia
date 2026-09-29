-- Prove2me | Theorems.Thm_CKLaneA3X_Step026_entryBounds_D_inner
-- name    : CKLaneA3X.Step026.entryBounds_D_inner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-25T00:38:40.661195+00:00
-- url     : https://prove2.me/theorems/da429d0f-1e59-479d-ba6e-0faa4c551fc7
-- title:
--   Exact rounded A3X input bounds for D_inner
-- statement:
--   The complete list of 24 rounded interval bounds for the coefficients of the exact input D_inner equals the displayed rational cache. Every entry preserves the original signed Laurent intervals, absolute-value maximum, sigma weight and upward rounding. These are exact equalities, not approximate numerical estimates. They provide one input to the still separate multiplication remainder bound.
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

theorem CKLaneA3X.Step026.entryBounds_D_inner : entryBounds D_inner.P = [(0 : ℚ), (2451053133237 : ℚ) / 1099511627776, (0 : ℚ), (7804116504201 : ℚ) / 1099511627776, (0 : ℚ), (13522484094635 : ℚ) / 549755813888, (0 : ℚ), (119550119947271 : ℚ) / 1099511627776, (0 : ℚ), (312317938243881 : ℚ) / 549755813888, (0 : ℚ), (2830579640422985 : ℚ) / 1099511627776, (0 : ℚ), (13458671255452477 : ℚ) / 1099511627776, (0 : ℚ), (30066067898006947 : ℚ) / 549755813888, (0 : ℚ), (254015746060502207 : ℚ) / 1099511627776, (0 : ℚ), (1121945005055783035 : ℚ) / 1099511627776, (0 : ℚ), (1183201062237625867 : ℚ) / 274877906944, (0 : ℚ), (3441045752199252747 : ℚ) / 1099511627776] := by sorry
