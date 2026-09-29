-- Prove2me | Theorems.Thm_CKLaneA3X_Step026_row21_slots16_17
-- name    : CKLaneA3X.Step026.row21_slots16_17
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-25T01:23:36.809709+00:00
-- url     : https://prove2.me/theorems/14080394-4b00-46cc-946e-69c408e3a2b4
-- title:
--   A3X output row 21, slots 16 and 17 Laurent blocks
-- statement:
--   The complete Laurent lists at sparse-list slots 16 and 17 of product output row 21 agree with the exact stored D_mInner lists. The stored pair contains 24 Laurent monomials, with sigma exponents 16 and 17. Product sparse-key equality and other slots remain separate obligations.
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

theorem CKLaneA3X.Step026.row21_slots16_17 (i : Fin 2) : (((TPoly.mulT D_m.P D_inner.P 24).getD 21 []).getD (16 + i.val) (0, [])).2 = ((D_mInner.P.getD 21 []).getD (16 + i.val) (0, [])).2 := by sorry
