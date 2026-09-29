-- Prove2me | Theorems.Thm_CKLaneA3X_Step026_row19_slots20_21
-- name    : CKLaneA3X.Step026.row19_slots20_21
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-25T01:14:48.80577+00:00
-- url     : https://prove2.me/theorems/db7104e6-358c-4f77-b224-4f53ae66205a
-- title:
--   A3X output row 19, slots 20 and 21 Laurent blocks
-- statement:
--   The complete Laurent lists at sparse-list slots 20 and 21 of product output row 19 agree with the exact stored D_mInner lists. The stored pair contains 22 Laurent monomials, with sigma exponents 20 and 21. Product sparse-key equality and other slots remain separate obligations.
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

theorem CKLaneA3X.Step026.row19_slots20_21 (i : Fin 2) : (((TPoly.mulT D_m.P D_inner.P 24).getD 19 []).getD (20 + i.val) (0, [])).2 = ((D_mInner.P.getD 19 []).getD (20 + i.val) (0, [])).2 := by sorry
