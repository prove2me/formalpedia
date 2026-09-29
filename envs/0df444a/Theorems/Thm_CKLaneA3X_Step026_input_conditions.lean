-- Prove2me | Theorems.Thm_CKLaneA3X_Step026_input_conditions
-- name    : CKLaneA3X.Step026.input_conditions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-25T00:52:57.736235+00:00
-- url     : https://prove2.me/theorems/47412c4f-a62c-486b-be42-b39582feecdb
-- title:
--   A3X input prefixes and truncation orders satisfy the multiplication conditions
-- statement:
--   The exact A3X inputs vanish through the required prefixes of lengths 2 and 1, the first input order is at least 2, and both shifted input orders reach truncation 24. This conjunction is exactly the first five captured numerical premises of the original Step026 multiplication step. It does not include polynomial equality or the remainder bound.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA3X/Step026.lean#L15

import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step026_data

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open CKLaneA3X

theorem CKLaneA3X.Step026.input_conditions : (zeroPrefix D_m.P 2 = true) ∧ (zeroPrefix D_inner.P 1 = true) ∧ (2 ≤ D_m.n) ∧ (24 ≤ 2 + D_inner.n) ∧ (24 ≤ 1 + D_m.n) := by sorry
