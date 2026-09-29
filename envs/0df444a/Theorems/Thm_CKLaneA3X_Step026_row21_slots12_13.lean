-- Prove2me | Theorems.Thm_CKLaneA3X_Step026_row21_slots12_13
-- name    : CKLaneA3X.Step026.row21_slots12_13
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-25T01:23:08.802361+00:00
-- url     : https://prove2.me/theorems/d085f990-24f4-4db3-bcac-b287aecbc5c3
-- title:
--   A3X output row 21, slots 12 and 13 Laurent blocks
-- statement:
--   The complete Laurent lists at sparse-list slots 12 and 13 of product output row 21 agree with the exact stored D_mInner lists. The stored pair contains 24 Laurent monomials, with sigma exponents 12 and 13. Product sparse-key equality and other slots remain separate obligations.
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

theorem CKLaneA3X.Step026.row21_slots12_13 (i : Fin 2) : (((TPoly.mulT D_m.P D_inner.P 24).getD 21 []).getD (12 + i.val) (0, [])).2 = ((D_mInner.P.getD 21 []).getD (12 + i.val) (0, [])).2 := by sorry
